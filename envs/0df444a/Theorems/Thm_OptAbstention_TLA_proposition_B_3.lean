-- Prove2me | Theorems.Thm_OptAbstention_TLA_proposition_B_3
-- name    : OptAbstention.TLA.proposition_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:18.315262+00:00
-- url     : https://prove2.me/theorems/cf2609b4-ae22-4e6e-9ce6-6efbcbb12243
-- title:
--   Proposition B.3: $H_{K_R(M)}(q)=\inf_t\{t+R\,\mathbb E_M[(q\cdot\psi-t)_+]\}$ (as printed; see insight I4)
-- statement:
--   Let $\Omega$ be a measurable space, $k\ge1$ and $\psi:\Omega\to\mathbb R^k$ measurable. For every distribution $M$ on $\Omega$, every $R\ge1$ and every $q\in\mathbb R^k$,
--   $$H_{K_R(M)}(q)=\inf_{t\in\mathbb R}\Big\{t+R\,\mathbb E_{x\sim M}\big[(q\cdot\psi(x)-t)_+\big]\Big\}.$$
--   It is the dual representation of the support function that reduces Lemma B.2 to uniform convergence over the class $\mathcal F$.
--
--   **Formalization Note.** The left side is a supremum in the extended reals ($-\infty$ when $K_R(M)=\emptyset$); the expectation on the right is a lower Lebesgue integral in $[0,\infty]$ and the infimum is in the extended reals. Stated as printed for every $M$ (see insight I4 on $R=1$).
--
--   Differences from the source:
--   - encoding: the setup of Lemma B.2 also fixes D, τ, δ → D, τ, δ omitted; reason: they do not occur in the statement
--   - encoding: H_A(q) = sup_{a∈A} q·a for nonempty A; E_M[(·)_+] real → sup in EReal (−∞ on ∅); E_M[(·)_+] a lower Lebesgue integral in [0,∞]; inf in EReal; reason: same values wherever the source's are defined
--   - encoding: E_{x∼M}[r(x)ψ(x)] for measurable r ∈ [0,R]^X → only r with rψ M-integrable contribute; reason: the expectation must be a vector of ℝ^k
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 38, Proposition B.3 (setup of Lemma B.2)

import Mathlib
import Definitions.Def_OptAbstention_TLA_CappedReweighting

open MeasureTheory

namespace OptAbstention.TLA

/-- Proposition B.3, p. 38 (setup of Lemma B.2): for every distribution `M`, `R ≥ 1` and
`q ∈ ℝ^k`, `H_{K_R(M)}(q) = inf_{t∈ℝ} {t + R E_{x∼M}[(q · ψ(x) − t)_+]}`, as printed. -/
theorem proposition_B_3 {Ω : Type} [MeasurableSpace Ω] (k : ℕ) (hk : 1 ≤ k)
    (ψ : Ω → Fin k → ℝ) (hψ : Measurable ψ) (M : Measure Ω) [IsProbabilityMeasure M]
    (R : ℝ) (hR : 1 ≤ R) (q : Fin k → ℝ) :
    supportFn (KR M ψ R) q =
      ⨅ t : ℝ, ((t : EReal) +
        ((ENNReal.ofReal R * ∫⁻ x, ENNReal.ofReal (∑ i, q i * ψ x i - t) ∂M : ENNReal) :
          EReal)) := by sorry

end OptAbstention.TLA
