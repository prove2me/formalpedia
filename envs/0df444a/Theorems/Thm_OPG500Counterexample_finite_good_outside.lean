-- Prove2me | Theorems.Thm_OPG500Counterexample_finite_good_outside
-- name    : OPG500Counterexample.finite_good_outside
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T04:06:51.882818+00:00
-- url     : https://prove2.me/theorems/02d9f846-d090-47cf-8042-3df62c1861ca
-- title:
--   Finite descent outside a closed family
-- statement:
--   Let $C$ be a type of objects with a complete finite list, a weak total preorder $\preceq$, and a strict relation $\prec$ compatible in the sense that $a\preceq b$ rules out $b\prec a$. Let each object have a code in a type $V$ with a binary combination, and let $I\subseteq V$ be closed under that combination.
--
--   Assume every object that is not good splits into two strictly smaller objects and that its code is the combination of their codes. If at least one object's code lies outside $I$, then
--
--   $$
--   \exists c,\quad c\text{ is good and }\operatorname{code}(c)\notin I.
--   $$
--
--   The finite list must contain every object; duplicates and ties are allowed.
-- source:
--   Candidate C12, frozen finite-descent declaration: https://github.com/vibemathing/problem-opg-500-geodesic-cycles/blob/a41fe59b4535851ea55f6e868e938b9aaf81e924/research/artifacts/candidates/opg500-a01-c12/FiniteDescent.lean

import Definitions.Def_opg500_weighted_cycle_models

namespace OPG500Counterexample

universe u v

/-- A complete finite table supplies a minimal good object outside any predicate
closed under the binary combination, provided every nongood object splits into
strictly smaller children and weak comparison excludes strict descent. -/
theorem finite_good_outside
    {C : Type u} {V : Type v}
    (combine : V → V → V) (code : C → V)
    (inside : V → Prop) (good : C → Prop)
    (leq smaller : C → C → Prop)
    (hrefl : ∀ a, leq a a)
    (htrans : ∀ a b c, leq a b → leq b c → leq a c)
    (htotal : ∀ a b, leq a b ∨ leq b a)
    (hcompat : ∀ a b, leq a b → ¬ smaller b a)
    (closed : ∀ a b, inside a → inside b → inside (combine a b))
    (split : ∀ c, ¬ good c → ∃ a, ∃ b,
      smaller a c ∧ smaller b c ∧ code c = combine (code a) (code b))
    (table : List C)
    (complete : ∀ c, c ∈ table)
    (outside : ∃ c, ¬ inside (code c)) :
    ∃ c, good c ∧ ¬ inside (code c) := by sorry

end OPG500Counterexample
