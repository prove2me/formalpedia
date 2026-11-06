-- Prove2me | Theorems.Thm_GradedReserve_lemma_3_2
-- name    : GradedReserve.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:39.127099+00:00
-- url     : https://prove2.me/theorems/f9a31953-b29e-493b-8b64-cba3e54c25d4
-- title:
--   Lemma 3.2 — acceptance levels, maximal filling and the revenue formulas
-- statement:
--   Let $n\ge2$ bidders have i.i.d. values with a density $f$ on $[0,1]$, positive on $(0,1)$, and let $F$ be regular (the standing assumptions of Section 3).
--   Fix a graded reserve $\pi$ and a symmetric Bayes–Nash equilibrium $\sigma$ of $G_\pi$, with probabilities of sale $s$, acceptance levels $w(t)=\inf\{v:s(v)\ge t\}$ ($w(t)=1$ if never reached), and
--   $$M(t)=\frac1t\int_0^tH(w(u))\,du,\qquad D(b)=n\int_0^bzQ(z)f(z)\,dz,\qquad B(t)=w(t)-\frac{H(w(t))-M(t)}{Q(w(t))}$$
--   ($B(t)=0$ if $w(t)=0$). Then for $t\in(0,1)$:
--
--   1. $U(w(t))=t\,\big(H(w(t))-M(t)\big)$;
--   2. $0\le B(t)\le w(t)$;
--   3. $B$ is non-decreasing;
--   4. the mechanism with $\pi_w(b)=\int_0^1\mathbf 1\{B(t)\le b\}\,dt$ is a graded-reserve auction with a symmetric Bayes–Nash equilibrium that has the same probabilities of sale (almost everywhere);
--   5. it fills every gap of the bid function with the largest acceptance probability compatible with incentives: the level thresholds $T(t)=\inf\{b:\pi(b)\ge t\}$ of the original mechanism satisfy $T(t)\ge B(t)$ for almost every $t$;
--   6. $\mathrm{Rev}_{\mathrm{rat}}=\int_0^1R_n(w(t))\,dt$;
--   7. $\mathrm{Rev}_{\mathrm{anc}}(G_\pi)\le\mathrm{Rev}_{\mathrm{anc}}(G_{\pi_w})=\mathbb E[V_{(1)}]-\int_0^1D(B(t))\,dt$.
--
--   The lemma turns the design problem over $G$ into a problem over non-decreasing level functions $w$, (5): minimize the anchored loss $\int_0^1D(B)$ subject to $\int_0^1R_n(w)\ge\tau$.
--
--   **Formalization Note** Clause 5 is read as the inequality $T\ge B$ a.e., which is the formal content the proof gives it.
--
--   Differences from the source:
--   - encoding: a distribution F on [0,1] whose density f is positive on (0,1) → IsValueDensity f (f measurable, ≥ 0 on [0,1], > 0 on (0,1), ∫₀¹ f = 1), F(v) = ∫₀^v f; reason: the paper's model; the same distributions
--   - encoding: F regular: φ strictly increasing → StrictMonoOn φ (0,1); reason: φ is defined where f > 0; the same laws
--   - encoding: symmetric BNE β, mixed strategies allowed (p.13), with an exit action → a Markov kernel σ from values to actions in ℝ; negative actions are exit, bids lie in [0,1], no mass above 1; reason: Lean convention (no measurable space on Option ℝ); the same strategies
--   - reading: a Bayes–Nash equilibrium (every type best-responds) → almost every type (for the value law) best-responds; reason: the paper's proofs work up to null sets of types ("apart from a null set", p.14); a single type has probability zero
--   - encoding: sells to the highest bidder with probability π(b₍₁₎); ties broken uniformly at random → W(b) = π(b) Σ_j C(n−1,j) a^j c^{n−1−j}/(j+1) against n − 1 i.i.d. opponents; reason: the same winning probability
--   - encoding: non-decreasing π : [0,1] → [0,1] → π : ℝ → ℝ, monotone with values in [0,1] on [0,1]; reason: only values on [0,1] are used; the same mechanisms
--   - encoding: U(v), the equilibrium utility of type v → interimUtility = sup over actions of the payoff, for every v; reason: equal to the equilibrium utility for almost every type; defined at every type
--   - encoding: s(v) = π(β(v)) and w(t) = inf{v : s(v) ≥ t} → s = q/Q (interim allocation over Q) and w(t) = essential infimum of {s ≥ t}, 1 if the level is never reached; reason: the proof reads generalized inverses up to null sets (p.14); equal for the pure ordered representation
--   - reading: it fills every gap of the bid function with the largest acceptance probability compatible with incentives → the thresholds T(t) = inf{b ∈ [0,1] : π(b) ≥ t} of the original π satisfy B(t) ≤ T(t) for a.e. t ∈ (0,1); reason: the proof's own formal content ("Hence T(t) ≥ B(t) almost everywhere", p.15)
--   - encoding: the threshold of a level that π never reaches is +∞ → T(t) = 1 for such a level; reason: B(t) ≤ w(t) ≤ 1, so the inequality T ≥ B is unaffected
--   - encoding: π_w(b) = ∫₀¹ 1{B(t) ≤ b} dt → Lebesgue measure of {t ∈ (0,1) : B(t) ≤ b}; reason: the same number
--   - encoding: Rev_anc(G_π) = E[V₍₁₎ π(V₍₁₎)], the revenue when all bidders are anchored → revRat of the truthful profile σ(v) = δ_v; reason: the revenue of anchored bidders; the same number
--   - encoding: R_n(r) = n ∫_r^1 φ Q f → n ∫_r^1 (v f(v) − (1 − F(v))) Q(v) dv; reason: equal wherever f > 0, i.e. almost everywhere; avoids x/0 = 0
--   - encoding: G_{π_w} has a symmetric BNE with the same probabilities of sale → a symmetric BNE σ' of G_{π_w} whose s equals that of σ for almost every type; reason: best responses are required for a.e. type, so probabilities of sale are determined only up to null sets of types
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Lemma 3.2, pp.5–6 (PDF 6–7); proof pp.14–16 (PDF 15–17)

import Mathlib
import Definitions.Def_GradedReserve_IsGradedReserve
import Definitions.Def_GradedReserve_IsRegular
import Definitions.Def_GradedReserve_IsSymBNE
import Definitions.Def_GradedReserve_IsValueDensity
import Definitions.Def_GradedReserve_acceptW
import Definitions.Def_GradedReserve_avgH
import Definitions.Def_GradedReserve_expMax
import Definitions.Def_GradedReserve_interimUtility
import Definitions.Def_GradedReserve_levelBid
import Definitions.Def_GradedReserve_levelW
import Definitions.Def_GradedReserve_lossD
import Definitions.Def_GradedReserve_oppCdfInt
import Definitions.Def_GradedReserve_revAnc
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_revRat
import Definitions.Def_GradedReserve_saleProb
import Definitions.Def_GradedReserve_threshold
import Definitions.Def_GradedReserve_typeMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Lemma 3.2** (Acceptance levels) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Lemma 3.2, pp.5–6, PDF 6–7; proof pp.14–16, PDF
15–17). Fix `G_π` with a symmetric BNE `σ`, its probabilities of sale `s`, levels `w`, and let `M`,
`D`, `B` be as in (4). Then
1. `U(w(t)) = t (H(w(t)) − M(t))` for `t ∈ (0, 1)`;
2. `0 ≤ B(t) ≤ w(t)`;
3. `B` is non-decreasing;
4. `π_w(b) = ∫₀¹ 1{B(t) ≤ b} dt` is a graded reserve and `G_{π_w}` has a symmetric BNE with
   the same probabilities of sale;
5. `π_w` fills every gap with the largest acceptance probability compatible with incentives: the
   level thresholds `T(t)` of `π` satisfy `T(t) ≥ B(t)` for almost every `t`;
6. `Rev_rat = ∫₀¹ R_n(w(t)) dt`;
7. `Rev_anc(G_π) ≤ Rev_anc(G_{π_w}) = E[V₍₁₎] − ∫₀¹ D(B(t)) dt`.

**Formalization Note.** Section 3's standing assumptions are hypotheses. Clause 5 is read as the
formal content the proof gives it ("Hence T(t) ≥ B(t) almost everywhere", p.15). `s` is the
interim allocation over `Q`, and `w` the essential infimum (see `saleProb`, `levelW`). -/
theorem lemma_3_2 (f : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n) (hf : IsValueDensity f) (hreg : IsRegular f)
    (π : ℝ → ℝ) (hπ : IsGradedReserve π) (σ : Kernel ℝ ℝ) (hσ : IsSymBNE f n π σ) :
    (∀ t ∈ Ioo (0:ℝ) 1, interimUtility f n π σ (levelW f n π σ t) =
      t * (oppCdfInt f n (levelW f n π σ t) - avgH f n (levelW f n π σ) t)) ∧
    (∀ t ∈ Ioo (0:ℝ) 1, 0 ≤ levelBid f n (levelW f n π σ) t ∧
      levelBid f n (levelW f n π σ) t ≤ levelW f n π σ t) ∧
    MonotoneOn (levelBid f n (levelW f n π σ)) (Ioo 0 1) ∧
    IsGradedReserve (acceptW f n (levelW f n π σ)) ∧
    (∃ σ' : Kernel ℝ ℝ, IsSymBNE f n (acceptW f n (levelW f n π σ)) σ' ∧
      saleProb f n (acceptW f n (levelW f n π σ)) σ' =ᵐ[typeMeasure f] saleProb f n π σ) ∧
    (∀ᵐ t ∂(volume.restrict (Ioo (0:ℝ) 1)),
      levelBid f n (levelW f n π σ) t ≤ threshold π t) ∧
    revRat f n π σ = ∫ t in (0:ℝ)..1, revCurve f n (levelW f n π σ t) ∧
    revAnc f n π ≤ revAnc f n (acceptW f n (levelW f n π σ)) ∧
    revAnc f n (acceptW f n (levelW f n π σ)) =
      expMax f n - ∫ t in (0:ℝ)..1, lossD f n (levelBid f n (levelW f n π σ) t) := by sorry

end GradedReserve
