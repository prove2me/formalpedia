-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_tendsto_weakDeriv_cutoff
-- name    : HunterPDE.Sobolev.tendsto_weakDeriv_cutoff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:34:18.860639+00:00
-- url     : https://prove2.me/theorems/bde41a5f-9c10-41e0-8bd2-b25dd806fff0
-- title:
--   Weak derivatives converge under expanding smooth cutoffs
-- statement:
--   Let $k\ge0$, $1\le p<\infty$, and $f\in W^{k,p}(\mathbb R^n)$. Let $\chi$ be smooth with compact support and equal to one in a neighborhood of zero. Put $\chi_j(x)=\chi(x/(j+1))$ for integers $j\ge0$. For every multi-index $\alpha$ of order at most $k$,
--
--   $$\|D^\alpha(f-\chi_j f)\|_{L^p(\mathbb R^n)}\longrightarrow0\qquad(j\longrightarrow\infty).$$
--
--   Here the derivatives are weak derivatives and their representatives are the chosen derivatives of Definition 3.23. No smoothness of $f$ is assumed. This convergence result applies to localization of arbitrary Sobolev functions, independently of how their smooth approximations are obtained. The order-zero and dimension-zero cases are included.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Definition 3.23 and proof of Theorem 3.24, printed pp. 58–59. The cutoff convergence is generalized to arbitrary Sobolev functions using the weak Leibniz rule of Propositions 3.16–3.17, p. 54; compact smooth membership follows by repeated integration by parts (Definitions 3.1–3.2, pp. 47–48).

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Topology.Order.Basic

open MeasureTheory Filter HunterPDE.Sobolev
open scoped Topology

theorem HunterPDE.Sobolev.tendsto_weakDeriv_cutoff {n k : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (f χ : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (hχ : IsTestFunction Set.univ χ) (hχone : χ =ᶠ[𝓝 0] 1)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) :
    Tendsto (fun j : ℕ => eLpNorm
      (weakDeriv Set.univ α (f - fun x => χ (((j : ℝ) + 1)⁻¹ • x) * f x))
      p volume) atTop (𝓝 0) := by sorry
