-- Prove2me | Theorems.Thm_MonoSkew_Main_proposition_2_7_iv
-- name    : MonoSkew.Main.proposition_2_7_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:19.954802+00:00
-- url     : https://prove2.me/theorems/c6c07472-2c0c-4226-8e8e-936b03428ab0
-- title:
--   Proposition 2.7(iv) — $J_{\gamma M}(x,v)=(J_{\gamma A}(x+\gamma z),J_{\gamma B^{-1}}(v-\gamma r))$
-- statement:
--   In the setting of Problems 1.1 and 1.2 ($A$, $B$ maximally monotone, $L$ bounded linear, $z\in\mathcal H$, $r\in\mathcal G$, and $M:(x,v)\mapsto(-z+Ax)\times(r+B^{-1}v)$ on $\mathcal K=\mathcal H\oplus\mathcal G$), for every $\gamma\in\,]0,+\infty[$, every $x\in\mathcal H$ and every $v\in\mathcal G$,
--   $$J_{\gamma M}(x,v)=\big(J_{\gamma A}(x+\gamma z),\,J_{\gamma B^{-1}}(v-\gamma r)\big).$$
--
--   This identity shows that the backward step of the forward–backward–forward method on $\mathcal K$ splits into a resolvent of $A$ and a resolvent of $B^{-1}$, computed in parallel.
--
--   **Formalization Note** Resolvents are given maps with the resolvent property: $J$ is a resolvent of $\gamma T$ if $\gamma^{-1}(w-Jw)\in T(Jw)$ for all $w$. The statement says: if $J_A$ is a resolvent of $\gamma A$ and $J_{B^{-1}}$ a resolvent of $\gamma B^{-1}$, then $(x,v)\mapsto(J_A(x+\gamma z),J_{B^{-1}}(v-\gamma r))$ is a resolvent of $\gamma M$. Since $M$ is maximally monotone (Proposition 2.7(i)), its resolvent is unique, so this is the paper's equality.
-- source:
--   Briceño-Arias and Combettes, A Monotone+Skew Splitting Model for Composite Monotone Inclusions in Duality, arXiv:1011.5517v1, p. 8, Proposition 2.7(iv)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace MonoSkew.Main

/-- Proposition 2.7(iv) (p. 8): for every `γ > 0`,
`J_{γM}(x, v) = (J_{γA}(x + γz), J_{γB⁻¹}(v − γr))`, stated as: if `JA` is the resolvent of
`γA` and `JBi` the resolvent of `γB⁻¹`, then the map
`(x, v) ↦ (JA(x + γz), JBi(v − γr))` is the resolvent of `γM`. -/
theorem proposition_2_7_iv {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G)
    (γ : ℝ) (hγ : 0 < γ) (JA : H → H) (hJA : IsResolvent γ A JA)
    (JBi : G → G) (hJBi : IsResolvent γ (opInv B) JBi) :
    IsResolvent γ (opM A B z r)
      (fun p : K H G => WithLp.toLp 2 (JA (p.fst + γ • z), JBi (p.snd - γ • r))) := by sorry

end MonoSkew.Main
