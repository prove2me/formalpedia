-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_lemma_2_2
-- name    : IIDMultiItem.TwoPoint.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:57:17.205069+00:00
-- url     : https://prove2.me/theorems/7821888e-5800-4c66-a306-1f13161c95c4
-- title:
--   Lemma 2.2 (weak duality, after Cai–Devanur–Weinberg) — identity (2.7); (2.5) with equality iff every positive-weight constraint is tight
-- statement:
--   Let $(T,f)$ be a type space with a prior, $\lambda$ a flow with virtual values $\Phi$ (2.6). Let $M=(x,s)$ be a mechanism (feasible: $x\in[0,1]$, (2.1)), $i$ a buyer and $v_{-i}$ reports of the others, and abbreviate $x(t)=x_i(t,v_{-i})$, $s(t)=s_i(t,v_{-i})$, $u(t)=u_i(t;v_{-i})=t\cdot x(t)-s(t)$. Then
--   $$\sum_t f(t)\sum_j\Phi_j(t)x_j(t)-\sum_t f(t)s(t)=\sum_{t',t}\lambda(t',t)\big(u(t')-u(t)-(t'-t)\cdot x(t)\big)+\sum_t\lambda(t,\bot)u(t).\tag{2.7}$$
--   In particular, if $M$ is DSIC and ex-post IR, then
--   $$\sum_t f(t)s(t)\le\sum_t f(t)\sum_j\Phi_j(t)x_j(t),\tag{2.5}$$
--   with equality if and only if every constraint of positive weight is tight ($u(t')=t'\cdot x(t)-s(t)$ whenever $\lambda(t',t)>0$, and $u(t)=0$ whenever $\lambda(t,\bot)>0$).
--
--   This is the duality step behind every upper bound in the paper: the expected payment of one buyer is at most her expected virtual surplus, under any flow.
--
--   Differences from the source:
--   - generalization: the type space supp(F)^m of a finite distribution F with product mass function f(t) = ∏_j f(t_j) → any finite type space Ts with a prior mass function (TypeSpace.IsPrior: f(t) > 0, ∑ f = 1) and arbitrary value vectors; reason: the identity and the bound use only the positivity of f; FinPrior.typeSpace F m satisfies IsPrior, so the statement specializes to the paper's, and the two-point type space of Section 3 is also an instance
--   - encoding: reports v_{-i} of the other buyers → a full profile v whose coordinate i is ignored (buyer i's report enters through Function.update v i t); reason: Lean convention; every v_{-i} is obtained and nothing depends on v i
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 12 (PDF 14), Lemma 2.2

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Model
import Definitions.Def_IIDMultiItem_TwoPoint_Flow

open scoped BigOperators

namespace IIDMultiItem.TwoPoint

/-- Lemma 2.2 (weak duality). For a flow `λ` with virtual values `Φ`, every mechanism `M`, buyer
`i` and reports `v_{-i}` satisfy the identity (2.7); if `M` is DSIC and ex-post IR, then (2.5)
holds, with equality iff every constraint of positive weight is tight. -/
theorem lemma_2_2 {T : Type} [Fintype T] {n m : ℕ} (Ts : TypeSpace T m) (hTs : Ts.IsPrior)
    (lam : Flow T) (hlam : lam.IsFlow Ts) (M : Mechanism T n m) (hM : M.Feasible)
    (i : Fin n) (v : Fin n → T) :
    let x : T → Fin m → ℝ := fun t => M.x (Function.update v i t) i
    let s : T → ℝ := fun t => M.s (Function.update v i t) i
    let u : T → ℝ := M.util Ts i v
    ((∑ t, Ts.pmf t * ∑ j, lam.virtualValue Ts t j * x t j) - ∑ t, Ts.pmf t * s t =
        (∑ t', ∑ t, lam.ic t' t * (u t' - u t - ∑ j, (Ts.val t' j - Ts.val t j) * x t j)) +
          ∑ t, lam.ir t * u t) ∧
    (M.DSIC_IR Ts →
      (∑ t, Ts.pmf t * s t ≤ ∑ t, Ts.pmf t * ∑ j, lam.virtualValue Ts t j * x t j) ∧
      ((∑ t, Ts.pmf t * s t = ∑ t, Ts.pmf t * ∑ j, lam.virtualValue Ts t j * x t j) ↔
        M.TightOn Ts i v lam)) := by sorry

end IIDMultiItem.TwoPoint
