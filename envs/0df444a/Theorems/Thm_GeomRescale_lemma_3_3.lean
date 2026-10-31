-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_3
-- name    : GeomRescale.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:40.298807+00:00
-- url     : https://prove2.me/theorems/5b3787ae-cd98-46cf-b6ee-19bc0da8eb63
-- title:
--   Lemma 3.3: a positive minimum over $B(f_\mu)$ yields a better set
-- statement:
--   Let $f$ be submodular with $f(\emptyset) = 0$, let $\mu \ge \max\{0, -f(V)\}$, and let $w : V \to \mathbb{R}$ satisfy $\min\{w^{\mathsf T} x : x \in B(f_\mu)\} > 0$. For $S = \mathrm{MinSet}(f_\mu, w)$, we have
--
--   $$f(S) < -\mu.$$
--
--   This holds for every order sorted by $w$ and every argmin in (4). It is the sliding update of Algorithm 1.
--
--   Differences from the source:
--   - generalization: $f$ integer valued (standing assumption of Section 3) → $f$ and $\mu$ real; reason: the proof uses no integrality; apply it to `fR f` and an integer $\mu$ for the page's statement
--   - encoding: $\min\{w^{\mathsf T} x : x \in B(f_\mu)\} > 0$ → $\forall x \in B(f_\mu),\ 0 < w^{\mathsf T} x$; reason: $B(f_\mu)$ is compact and nonempty, so the two conditions agree
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.3, p.7

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_IsSortedBy
import Definitions.Def_GeomRescale_IsMinSet
import Definitions.Def_GeomRescale_enlarge

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.3 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.3, p.7): for `μ ≥ max {0, −f(V)}` and `w : V → ℝ` with
`min {wᵀx : x ∈ B(f_μ)} > 0`, every `S = MinSet(f_μ, w)` has `f(S) < −μ`.

**Formalization Note.** The positive minimum is written `∀ x ∈ B(f_μ), 0 < wᵀx`, which is the same
condition as `B(f_μ)` is compact and nonempty. The statement holds for every order `σ` sorted by `w`
and every argmin of (4). -/
theorem lemma_3_3 {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) (w : Fin n → ℝ)
    (hw : ∀ x ∈ baseB (enlarge f μ), 0 < w ⬝ᵥ x)
    (σ : Equiv.Perm (Fin n)) (hσ : IsSortedBy w σ) (S : Finset (Fin n))
    (hS : IsMinSet (enlarge f μ) σ S) :
    f S < -μ := by sorry

end GeomRescale
