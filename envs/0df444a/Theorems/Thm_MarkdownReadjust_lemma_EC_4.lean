-- Prove2me | Theorems.Thm_MarkdownReadjust_lemma_EC_4
-- name    : MarkdownReadjust.lemma_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:43.683222+00:00
-- url     : https://prove2.me/theorems/d8d5b6eb-7aff-4859-99f4-9b1925a4b241
-- title:
--   Lemma EC.4 — the bad event is rare
-- statement:
--   Fix a model, $T>0$, an integer $x_0\ge1$ and $\alpha>1/2$, and consider the asymptotic setting $x_0^{(k)}=kx_0$, $T^{(k)}=kT$ with update times (14) and shifts (15). There is a constant $K>0$ such that for all $k>K$ and all $N\ge1$ satisfying the condition of Theorem 4,
--
--   $$
--   \mathbb P(\mathcal G^c)\le 3N\exp\Big(-0.05\,\big(\ln(x_0^{(k)}+1)\big)^{2\alpha}\Big),
--   $$
--
--   where $\mathbb P$ is the law of the uncapped process of the $k$-th problem. Since $2\alpha>1$, the bound decays faster than any power of $k$.
--
--   Differences from the source:
--   - generalization: valuation c.d.f. F with a density f whose derivative f′ is supported on [0,V), A1–A3 → F̄ continuous and strictly decreasing on [0,V] with F̄(0)=1, F̄(V)=0, plus A2 for R(ρ)=ρF̄⁻¹(ρ) on [0,1], |R| ≤ C on [0,1], and A3's twice differentiability with |R′|, |R″| ≤ C on the open interval (0,1) only; reason: the results use F̄ only through these properties (A1 follows from continuity at V); every model of the paper satisfies them, and nothing is required of R′, R″ at the endpoints ρ = 0, 1
--   - encoding: expectations and probabilities of the uncapped process (Ŝₙ Poisson with mean λ(t_{n+1}−tₙ)ρ̂ₙ) → integrals and measures under hatLaw, the sequential Poisson law of (Ŝ₀,…,Ŝ_N) on Fin (N+1) → ℕ; reason: it is the joint law of the uncapped sales; same values
--   - reading: assume that N satisfies the condition stated in the theorem; there exists K such that for all k > K → the condition evaluated at x₀^{(k)} = kx₀, and K chosen before k and N (uniform over all admissible N); reason: the proof (p.ec24) applies the condition at x₀^{(k)} and lets N grow with k; the uniform statement implies the one for each fixed admissible N
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Lemma EC.4, p.ec14 (proof pp.ec21–ec24)

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_seqPoissonLaw
import Definitions.Def_MarkdownReadjust_hatLaw
import Definitions.Def_MarkdownReadjust_goodEvent
import Definitions.Def_MarkdownReadjust_NCond

open MeasureTheory

namespace MarkdownReadjust

/-- **Lemma EC.4, p.ec14** (Chen–Jasin, SSRN 3740871). Consider the asymptotic setting of
Theorem 4 (`x₀^{(k)} = k x₀`, `T^{(k)} = k T`) and `N` satisfying the condition of the theorem.
There is `K > 0` such that for all `k > K`,
`P(𝒢ᶜ) ≤ 3N exp(−0.05 (ln(x₀^{(k)} + 1))^{2α})`.

**Formalization Note.** The model, `T > 0`, the integer `x₀ ≥ 1` and `α > 1/2` are fixed; `K`
is chosen before `k` and `N`, so it is uniform over all `N ≥ 1` satisfying the condition of
Theorem 4 at `x₀^{(k)}` (the proof lets `N` grow with `k`). `P` is the uncapped law of the k-th
problem. -/
theorem lemma_EC_4 (M : Model) (T : ℝ) (hT : 0 < T) (x0 : ℕ) (hx0 : 1 ≤ x0) (α : ℝ)
    (hα : 1 / 2 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ, K < k → ∀ N : ℕ, 1 ≤ N → NCond α N (k * x0) →
      (hatLaw M α N (k * x0) (k * T)) (goodEvent M α N (k * x0) (k * T))ᶜ
        ≤ ENNReal.ofReal
            (3 * N * Real.exp (-0.05 * Real.log (((k * x0 : ℕ) : ℝ) + 1) ^ (2 * α))) := by sorry

end MarkdownReadjust
