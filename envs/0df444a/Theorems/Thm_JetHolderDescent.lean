-- Prove2me | Theorems.Thm_JetHolderDescent
-- name    : JetHolderDescent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:09:41.71836+00:00
-- url     : https://prove2.me/theorems/e69af3a9-3efc-42ab-a1cd-cea05090508c
-- title:
--   Jet Holder Descent: Jet Holder Descent
-- statement:
--   JET DESCENT ON A BOUNDED CONVEX SET.  On an open convex `U` of diameter at most `d`, sup
--   bounds on the jets of `Φ` up to order `n+1` yield BOTH a sup bound and a `κ`-Holder estimate on
--   the order-`n` jet, at the cost of one single factor `θ ≥ 1` depending only on `κ` and `d`.
--
--   The factor is produced BEFORE the target space `Z`, the set `U`, the order `n`, the constant `L`
--   and the map `Φ`, and is quantified existentially: what a consumer needs is that ONE
--   diameter-dependent factor makes the descent work at every instantiation, not the factor's
--   formula.  Returning `1 ≤ θ` rather than `0 < θ` is deliberate — it is what lets a consumer
--   compare `L` with `L * θ` — and `0 < θ` follows by `lt_of_lt_of_le one_pos`.
--
--   The two conclusions are what a `C^{n,κ}` statement consists of, and the order-`n` Holder half is
--   the one that is NOT available from a composition or product bound: those control a norm at a
--   point, whereas a Holder seminorm is a two-point difference.  The route is the mean value
--   inequality on the convex `U`, applied to the order-`n` jet, whose Frechet derivative has norm
--   `‖D^(n+1) Φ‖ ≤ L`; that gives a LIPSCHITZ estimate, and the diameter bound then upgrades
--   Lipschitz to `κ`-Holder.  That upgrade is where `θ` is spent and where it must be: on a set of
--   diameter `d` one has `t ≤ θ t^κ` for `0 ≤ t ≤ d`, by splitting `t = t^(1-κ) t^κ` and bounding
--   `t^(1-κ) ≤ d^(1-κ) ≤ θ`, and the factor cannot be dispensed with, since `t` and `t^κ` are not
--   comparable near `t = 1` without it.
--
--   Note that `0 < d` is NOT a hypothesis: the descent never needs it.  A degenerate or empty `U`
--   satisfies the diameter bound vacuously and the conclusion holds for it as well.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/JetHolderDescent.lean#L25-L80
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/JetHolderDescent.lean#L25-L80

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_JetHolderDescent
set_option autoImplicit false

theorem JetHolderDescent (κ d : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ θ : ℝ, 1 ≤ θ ∧
      ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (U : Set Plane),
        IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
        ∀ (n : ℕ) (L : ℝ) (Φ : Plane → Z), 0 ≤ L → ContDiffOn ℝ (⊤ : ℕ∞) Φ U →
        (∀ i ≤ n + 1, ∀ x ∈ U, ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) →
        ((∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i Φ x‖ ≤ L * θ) ∧
          ∀ x ∈ U, ∀ y ∈ U,
            ‖iteratedFDeriv ℝ n Φ x - iteratedFDeriv ℝ n Φ y‖ ≤ L * θ * ‖x - y‖ ^ κ) := by sorry
