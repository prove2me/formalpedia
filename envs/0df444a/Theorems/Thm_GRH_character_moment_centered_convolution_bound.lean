-- Prove2me | Theorems.Thm_GRH_character_moment_centered_convolution_bound
-- name    : GRH.character_moment_centered_convolution_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T17:22:09.618007+00:00
-- url     : https://prove2.me/theorems/7e80ecde-a7e3-4024-8a16-1b3e2d240ff4
-- title:
--   Powers of a character sum are bounded by centered convolution coefficients
-- statement:
--   Let $U$ be a finite set of residues for which the supplied multiplication and inverse-multiplication maps are inverse permutations. Let a Dirichlet character sum to zero on $U$. After $j$ convolution squares of an initial row $f$, the $2^j$-th power of the norm of its character sum is at most the sum of the absolute differences between the final row and any fixed natural number.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/1b3886ba-6475-4979-b196-63418759603e. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_CharacterMoment

open GRH.CharacterMoment

theorem GRH.character_moment_centered_convolution_bound (q : ℕ) (χ : DirichletCharacter ℂ q) (U : Finset ℕ)
    (iv f : ℕ → ℕ) (rows : List (Array ℕ)) (c : ℕ) (hp : Permutes q U iv)
    (hz : ∑ a ∈ U, χ (a:ZMod q) = 0) (hrows : Rows q U iv f rows) :
    ‖∑ a ∈ U, (f a:ℂ)*χ (a:ZMod q)‖^(2^rows.length) ≤ (deviation U (lastRow f rows) c:ℝ) := by sorry
