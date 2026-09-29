-- Prove2me | Theorems.Thm_Maldacena1999_AdS_invariant_of_preserves_eta
-- name    : Maldacena1999.AdS_invariant_of_preserves_eta
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:41:22.427837+00:00
-- url     : https://prove2.me/theorems/6ecfc769-3695-4ec8-8290-0ed2558b2b91
-- title:
--   $O(2,p+1)$ preserves the $\mathrm{AdS}_{p+2}$ hyperboloid
-- statement:
--   Let $p\ge0$, $R\in\mathbb R$, and let $\eta=\mathrm{diag}(-1,-1,1,\dots,1)$ be the metric of $\mathbb R^{2,p+1}$. If a real $(p+3)\times(p+3)$ matrix $A$ satisfies
--   $$A^{\mathsf T}\eta A=\eta,$$
--   then for every $X\in\mathrm{AdS}_{p+2}(R)$, i.e. $\langle X,X\rangle_\eta=-R^2$, also $AX\in\mathrm{AdS}_{p+2}(R)$.
--
--   This is the statement that the symmetry group $SO(2,p+1)$ — the conformal group of the $(p+1)$-dimensional boundary theory, e.g. $SO(2,4)$ for D3-branes — acts on anti-de Sitter space.
--
--   **Formalization Note** The statement is made for the whole group $O(2,p+1)=\{A : A^{\mathsf T}\eta A=\eta\}$, which contains $SO(2,p+1)$.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://doi.org/10.1023/A:1026654312961 (arXiv:hep-th/9711200), Appendix, sentence after (A.1), p. 1130

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

namespace Maldacena1999

theorem AdS_invariant_of_preserves_eta (p : ℕ) (R : ℝ)
    (A : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ)
    (hA : A.transpose * Matrix.diagonal (ambientSign p) * A = Matrix.diagonal (ambientSign p))
    (X : Fin (p + 3) → ℝ) (hX : X ∈ AdS p R) :
    A.mulVec X ∈ AdS p R := by
  sorry

end Maldacena1999
