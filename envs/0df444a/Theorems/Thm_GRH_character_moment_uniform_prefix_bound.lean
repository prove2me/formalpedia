-- Prove2me | Theorems.Thm_GRH_character_moment_uniform_prefix_bound
-- name    : GRH.character_moment_uniform_prefix_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T17:22:13.03395+00:00
-- url     : https://prove2.me/theorems/0bed744b-4f4a-45e3-a7aa-77a59cc9f74b
-- title:
--   Multiplicative moment certificates bound every centered prefix of a nonprincipal character
-- statement:
--   If a period $q$ admits a multiplicative moment profile with scale $S$ and bounds $B$, then every nonprincipal character modulo $q$ satisfies $S|\sum_{k=1}^n\chi(k)-1|\le B(n\bmod q)$ for every $n$, including complete periods.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/1b3886ba-6475-4979-b196-63418759603e. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_CharacterMoment

open GRH.CharacterMoment

theorem GRH.character_moment_uniform_prefix_bound (q S : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ≠1)
    (B : ℕ → ℕ) (hp : Profile q S B) (n : ℕ) :
    (S:ℝ)*‖(∑ k ∈ Finset.range n,χ ((k+1:ℕ):ZMod q))-1‖ ≤ (B (n%q):ℝ) := by sorry
