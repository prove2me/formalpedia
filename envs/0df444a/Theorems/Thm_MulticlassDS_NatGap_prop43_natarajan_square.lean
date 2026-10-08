-- Prove2me | Theorems.Thm_MulticlassDS_NatGap_prop43_natarajan_square
-- name    : MulticlassDS.NatGap.prop43_natarajan_square
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:49:08.562895+00:00
-- url     : https://prove2.me/theorems/4eac6f9e-1b8c-44d9-8a63-1a6d46286633
-- title:
--   Proposition 43, p. 29 — B(C, r) has Natarajan dimension ≥ 2 iff C has a square with r(v₀) = r(v₂), r(v₁) = r(v₃)
-- statement:
--   Let $C$ be a $d$-dimensional good complex over $V$, let $r$ be a proper coloring of $C$, and let $B = B(C, r) \subseteq V^{d+1}$ be the pseudo-cube defined by $C$ and $r$. The following are equivalent:
--
--   1. there is a square $v_0 \to v_1 \to v_2 \to v_3 \to v_0$ in $C$ with $r(v_0) = r(v_2)$ and $r(v_1) = r(v_3)$;
--   2. the Natarajan dimension of $B$, viewed as a class of functions $[d+1] \to V$, is at least $2$:
--   $$d_N(B) \ge 2 .$$
--
--   This translates the Natarajan dimension of a pseudo-cube into a local combinatorial property of the complex.
--
--   **Formalization Note** $B$ is a class over the domain `Fin (d + 1)` with labels in $V$, and $d_N(B)$ is the shared $\mathbb N_\infty$-valued Natarajan dimension.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 29, Proposition 43

import Mathlib
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_MulticlassDS_NatGap_Complexes

namespace MulticlassDS.NatGap

theorem prop43_natarajan_square {V : Type*} (C : Set (Finset V)) (d : ℕ)
    (hC : IsGood C d) (r : V → Fin (d + 1)) (hr : IsProperColoring C d r) :
    (∃ v₀ v₁ v₂ v₃ : V, IsSquare C v₀ v₁ v₂ v₃ ∧ r v₀ = r v₂ ∧ r v₁ = r v₃) ↔
      2 ≤ natarajanDim (pseudoCubeOf C d r) := by sorry

end MulticlassDS.NatGap
