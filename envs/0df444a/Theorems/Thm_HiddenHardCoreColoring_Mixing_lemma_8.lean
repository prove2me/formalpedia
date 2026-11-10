-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_8
-- name    : HiddenHardCoreColoring.Mixing.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:59:58.249418+00:00
-- url     : https://prove2.me/theorems/782a42b0-4332-4d28-8e37-30653358d0c4
-- title:
--   Lemma 8 — global comparison: ∑_c ‖L_c f‖² ≥ (θ_γ/24)⟨f,Lf⟩ − O_γ(1/Δ)(‖Lf‖² + ⟨f,Lf⟩)
-- statement:
--   For every $\gamma>0$ there are constants $\theta_\gamma\in(0,1]$ and $B_\gamma>0$, depending only on $\gamma$, such that for every finite simple graph on $n\ge1$ vertices with $\deg(v)\le\Delta$, every $q\ge(1+1/e+\gamma)\Delta$ with $\Delta\ge\max\{3,2/\gamma\}$, and every $f\in L^2(\mu)$,
--   $$\sum_{c\in[q]}\|L_cf\|_\mu^2\ge\frac{\theta_\gamma}{24}\langle f,Lf\rangle_\mu-\frac{B_\gamma}{\Delta}\Big(\|Lf\|_\mu^2+\langle f,Lf\rangle_\mu\Big).$$
--   The second term is the paper's $O_\gamma(1/\Delta)\big(\|Lf\|_\mu^2+\langle f,Lf\rangle_\mu\big)$.
--
--   Together with Lemma 7 this gives the integrated Bochner inequality of Theorem 1; the constant $1/e$ comes from the hard-core uniqueness threshold.
--
--   **Formalization Note** Functions on $\Omega$ are all real functions on the subtype of proper colorings; operators are matrices on $\Omega$ acting by $(Mf)(\sigma)=\sum_\tau M(\sigma,\tau)f(\tau)$, and $\langle f,g\rangle_\mu$ is the uniformly weighted sum.
--
--   Differences from the source:
--   - reading: error term O_γ(1/Δ)(‖Lf‖² + ⟨f, Lf⟩) → (B_γ/Δ)(‖Lf‖² + ⟨f, Lf⟩) with B_γ > 0 chosen after γ and θ_γ, before the graph, Δ, q and f; reason: the uniform meaning of O_γ; the proof on p.23 bounds the error by C₀e(1 + ea/Δ)/Δ with a = 3/θ_γ
--   - encoding: standing assumption q ≥ Δ + 3 → not written; reason: implied by q ≥ (1 + 1/e + γ)Δ and Δ ≥ max{3, 2/γ} (proved in Solutions/verification/HiddenHardCoreColoring_Mixing_Checks.lean); no instance is lost
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 8, eq. (12), p.10; proof pp.22–23

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 8** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.10, eq. (12)). For every `γ > 0` there are `θ_γ ∈ (0, 1]` and `B_γ > 0`
(the constant of the `O_γ(1/Δ)` term) such that if `q ≥ (1 + 1/e + γ)Δ` and `Δ ≥ max{3, 2/γ}`, then for
every `f`, `∑_c ‖L_c f‖²_µ ≥ (θ_γ/24)⟨f, Lf⟩_µ − (B_γ/Δ)(‖Lf‖²_µ + ⟨f, Lf⟩_µ)`. -/
theorem lemma_8 (γ : ℝ) (hγ : 0 < γ) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∃ B : ℝ, 0 < B ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (Δ q : ℕ), (∀ v, G.degree v ≤ Δ) → (1 + 1 / Real.exp 1 + γ) * (Δ : ℝ) ≤ (q : ℝ) →
        3 ≤ Δ → 2 / γ ≤ (Δ : ℝ) → ∀ f : Col G q → ℝ,
          θ / 24 * ip G q f (Lap G q *ᵥ f) -
              B / (Δ : ℝ) * (sqNorm G q (Lap G q *ᵥ f) + ip G q f (Lap G q *ᵥ f)) ≤
            ∑ c : Fin q, sqNorm G q (Lc G q c *ᵥ f) := by sorry

end HiddenHardCoreColoring.Mixing
