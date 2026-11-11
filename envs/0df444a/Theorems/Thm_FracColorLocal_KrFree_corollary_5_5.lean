-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_corollary_5_5
-- name    : FracColorLocal.KrFree.corollary_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:18.826208+00:00
-- url     : https://prove2.me/theorems/c940aaa8-ff34-43b1-ac10-b31dc11a168c
-- title:
--   Corollary 5.5 — at a positive global maximizer of U over nonnegative weights, T_G(w) ≤ 2C△rS
-- statement:
--   Fix an integer $r\ge4$. Let $G$ be a finite $K_r$-free graph and $u>0$. If $w>0$ is a global maximizer of $U_{G,u}$ over nonnegative vertex weights, then (with $\theta_v=2r\xi_v/w(v)$ in Lemma 5.1)
--
--   $$T_G(w)\ \le\ 2C_\triangle\,r\,S,\qquad S=\sum_vu(v)w(v),$$
--
--   where $C_\triangle=2^{t_*}$ is the constant of Lemma 5.1. With Lemma 4.3 and $c=c_r$ of (6.1) this gives a vertex with nonnegative gain, which closes the induction for Theorem 1.7.
--
--   Differences from the source:
--   - generalization: $C_\triangle$ "the constant of Lemma 5.1" → the explicit $C_\triangle=2^{t_*}$; reason: it is the value §8 fixes for Lemma 5.1, and the item matches the Lemma 5.1 item.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 24 (PDF 25), Corollary 5.5 (r ≥ 4 fixed in §5.3, p. 21)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_FracColorLocal_KrFree_Constants
import Definitions.Def_FracColorLocal_KrFree_Potential

open OAI.CliqueFreeIndependence.WeightedGraph

namespace FracColorLocal.KrFree

/-- Corollary 5.5: at a positive global maximizer `w` of `U_{G,u}` over nonnegative weights,
`T_G(w) ≤ 2 C△ r S` (with `C△ = 2^{t∗}` the constant of Lemma 5.1). -/
theorem corollary_5_5 {V : Type*} [Fintype V] (r : ℕ) (hr : 4 ≤ r) (G : SimpleGraph V)
    (hG : G.CliqueFree r) (u w : V → ℝ) (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v)
    (hmax : ∀ w' : V → ℝ, (∀ v, 0 ≤ w' v) → potential G u w' ≤ potential G u w) :
    triangleMass G w ≤ 2 * (Ctri : ℝ) * r * sObj u w := by sorry

end FracColorLocal.KrFree
