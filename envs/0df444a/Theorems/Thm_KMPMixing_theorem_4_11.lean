-- Prove2me | Theorems.Thm_KMPMixing_theorem_4_11
-- name    : KMPMixing.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:36.179357+00:00
-- url     : https://prove2.me/theorems/c07a5add-0982-4435-8735-feb57dd83f64
-- title:
--   Theorem 4.11 + Remark 4.12 — KMP mixes in $O(\gamma^{-1}(\log d+\log(1/\varepsilon)))$ steps uniformly in $t$ (corrected: Remark 4.12 for ε < 1/2 with factor 1 + 1/log(1/(2ε)))
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every positive integer $t$, every integer $d\ge2$ and every connected graph $G=(V=[d],E)$. Let $M=M^{(t,G)}_{\mathrm{KMP}}$, $\pi_{\mathrm{KMP}}$ the uniform law on $\Delta_G$, $T^{\mathrm{mix}}(\varepsilon)=\min\{k\in\mathbb N:\max_r\|M^k(r,\cdot)-\pi_{\mathrm{KMP}}\|_{\mathrm{TV}}\le\varepsilon\}$, and $\gamma=1-\lambda_2(M^{(1,G)}_{\mathrm{KMP}})$ the spectral gap of the single-particle walk.
--
--   1. (Theorem 4.11) For every $\varepsilon\in(0,1)$ the minimum defining $T^{\mathrm{mix},(t,G)}_{\mathrm{KMP}}(\varepsilon)$ is attained, and
--   $$
--   T^{\mathrm{mix},(t,G)}_{\mathrm{KMP}}(\varepsilon)\le\frac C\gamma\big(\log d+\log(1/\varepsilon)\big).
--   $$
--   2. (Remark 4.12, corrected) For every $\varepsilon\in(0,1/2)$,
--   $$
--   T^{\mathrm{mix},(t,G)}_{\mathrm{KMP}}(\varepsilon)\le C\Big(1+\frac1{\log(1/(2\varepsilon))}\Big)\,T^{\mathrm{mix},(1,G)}_{\mathrm{KMP}}(\varepsilon)\,\big(\log d+\log(1/\varepsilon)\big).
--   $$
--
--   The mixing time does not depend on the number of particles $t$; it is the single-particle relaxation time times $\log d+\log(1/\varepsilon)$. Logarithms are natural.
--
--   Differences from the source:
--   - reading: $T^{\mathrm{mix}}=O(\cdot)$ → one constant $C>0$ quantified before $t,d,G,\varepsilon$; reason: the abstract, Theorem 1.1 ("uniformly over all particle numbers $t$") and Theorem 5.5's restatement ("There is an absolute constant $C>0$") fix the constant as absolute
--   - encoding: $T^{\mathrm{mix}}(\varepsilon)=\min\{\dots\}$ → `MarkovMixing.mixingTime` (an infimum over $\mathbb N$) together with the clause $\delta(T^{\mathrm{mix}}(\varepsilon))\le\varepsilon$; reason: Lean's infimum of an empty set is $0$, the attainment clause makes the minimum exist as in the source
--   - encoding: $\gamma$ (spectral gap, $\lambda_2$ in absolute value) → `MarkovMixing.absSpectralGap` of the $t=1$ KMP chain; reason: the source's $\lambda_2$ is the second largest eigenvalue in absolute value (Fact 2.4)
--   - correction: Remark 4.12, $T^{\mathrm{mix},(t,G)}(\varepsilon)=O(T^{\mathrm{mix},(1,G)}(\varepsilon)(\log d+\log(1/\varepsilon)))$ for $\varepsilon\in(0,1)$ → for $\varepsilon\in(0,1/2)$ with the extra factor $1+1/\log(1/(2\varepsilon))$; reason: the printed remark is false: on $G=K_2$ with $t=2$ and $\varepsilon=1/2$, $T^{\mathrm{mix},(1,G)}(1/2)=0$ (one particle starts at distance $1/2$) while $T^{\mathrm{mix},(2,G)}(1/2)\ge1$ (two particles start at distance $2/3$), so the right side is $0$ and the left side is at least $1$; the cited [LP17, Thm 12.5] bound $(t_{\mathrm{rel}}-1)\log(1/(2\varepsilon))$ is vacuous for $\varepsilon\ge1/2$ and degenerates as $\varepsilon\uparrow1/2$, which the factor records; the factor is bounded for $\varepsilon$ bounded away from $1/2$, so this is the printed remark at every such accuracy
-- source:
--   Chen et al., arXiv:2609.38044, Theorem 4.11 and Remark 4.12, p.29 (PDF p.31); Theorem 1.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
open MarkovMixing

namespace KMPMixing

/-- **Theorem 4.11 and Remark 4.12 (corrected)** (arXiv:2609.38044, p.29 (PDF p.31); the formal
version of Theorem 1.1, p.3 (PDF p.5)). There is an absolute constant `C > 0` such that for every
positive integer `t`, every integer `d ≥ 2` and every connected graph `G = ([d], E)`, with
`γ = γ^{(1,G)}_KMP` the spectral gap of the single-particle walk `M^{(1,G)}_KMP`:

(a) (Theorem 4.11) for every `ε ∈ (0, 1)`, the mixing time `T^{mix,(t,G)}_KMP(ε)` is attained and
`T^{mix,(t,G)}_KMP(ε) ≤ (C/γ) · (log d + log(1/ε))`;

(b) (Remark 4.12, corrected) for every `ε ∈ (0, 1/2)`,
`T^{mix,(t,G)}_KMP(ε) ≤ C · (1 + 1/log(1/(2ε))) · T^{mix,(1,G)}_KMP(ε) · (log d + log(1/ε))`.

**Formalization Note** `O(·)` is one absolute constant, quantified before `t, d, G, ε` (uniform in
`t`, as the abstract and Theorem 1.1 say). `T^mix(ε)` is `MarkovMixing.mixingTime`, an `sInf`
over `ℕ`; clause (a) states that it is attained (`δ(T^mix(ε)) ≤ ε`). `γ` is
`MarkovMixing.absSpectralGap` of the `t = 1` KMP chain (`λ₂` in absolute value, Fact 2.4).
`log` is the natural logarithm. Remark 4.12 as printed is false for `ε ∈ [1/2, 1)` (on `K₂` with
`t = 2`, `ε = 1/2`: the right side is `0`, the left side is `1`); clause (b) restricts to
`ε < 1/2` and carries the factor `1 + 1/log(1/(2ε))`, bounded for `ε` bounded away from `1/2`. -/
theorem theorem_4_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t d : ℕ), 0 < t → 2 ≤ d →
      ∀ (G : SimpleGraph (Fin d)) [DecidableRel G.Adj], G.Connected →
        (∀ ε : ℝ, 0 < ε → ε < 1 →
          distStationary (kmpChain G t) (uniformDist (State d t))
              (mixingTime (kmpChain G t) (uniformDist (State d t)) ε) ≤ ε ∧
          (mixingTime (kmpChain G t) (uniformDist (State d t)) ε : ℝ) ≤
            C / absSpectralGap (kmpChain G 1) * (Real.log d + Real.log (1 / ε))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          (mixingTime (kmpChain G t) (uniformDist (State d t)) ε : ℝ) ≤
            C * (1 + 1 / Real.log (1 / (2 * ε))) *
              (mixingTime (kmpChain G 1) (uniformDist (State d 1)) ε : ℝ) *
              (Real.log d + Real.log (1 / ε))) := by sorry

end KMPMixing
