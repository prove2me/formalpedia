-- Prove2me | Theorems.Thm_Holant3Dich_proposition_9_10
-- name    : Holant3Dich.proposition_9_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:05:51.61072+00:00
-- url     : https://prove2.me/theorems/085b39a1-7ba1-4aef-b180-a581d7453dfa
-- title:
--   Proposition 9.10: a signature of type $\mathfrak F$ realizes a ternary signature of type $\mathfrak F$
-- statement:
--   Let $\mathfrak F$ be one of the nine tractable types $\mathfrak A_2,\mathfrak A_3,\mathfrak B_2,\mathfrak B_3,\mathfrak C^0,\mathfrak C^1_2,\mathfrak C^1_s,\mathfrak C^1_z,\mathfrak C^1_g$, and let $F$ be a nondegenerate symmetric signature of arity $n\ge3$ of type $\mathfrak F$. Then there are $u_1,\dots,u_k\in\mathbb C^3$, $k=n-3$, such that connecting $u_1,\dots,u_k$ to $F$ gives a ternary signature $G$ of type $\mathfrak F$; moreover, for this $G$, every orthogonal $T$ for which $TF$ is of the defining form of $\mathfrak F$ makes $TG$ of the defining form as well.
--
--   This lets the dichotomy for ternary signatures (Theorem 8.13) be lifted to every arity, with the same transformation $T$.
--
--   Differences from the source:
--   - reading: "there exists u1, …, uk … G of type 𝔉. Further, if T … TF is of the defining form, then TG is of the defining form as well" → one list u₁, …, u_k serves both sentences, for every such T; reason: the literal reading: G is the signature of the first sentence; it is the stronger reading
--   - encoding: connecting u1, …, uk to F → contracting u₁, u₂, … one after another into the last remaining input (`contractMany`); reason: F is symmetric, so the inputs used do not matter
--   - encoding: domain {B, G, R} (Boolean domain {0, 1}) → `Fin 3` with B, G, R = 0, 1, 2 (`Fin 2`); reason: Lean convention; same instances
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Proposition 9.10, p.90

import Mathlib
import Definitions.Def_Holant3Dich_TractType

set_option autoImplicit false

namespace Holant3Dich

/-- **Proposition 9.10 (realizing a ternary signature of the same type).** Cai–Ihm, *Group Action
and Spin Representation Lead to a Holant\* Complexity Dichotomy on Domain Size 3*, STOC 2027
submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Proposition 9.10, p.90: "Let 𝔉
be a tractable type 𝔄2, 𝔄3, 𝔅2, 𝔅3, ℭ0, ℭ1_2, ℭ1_s, ℭ1_z, or ℭ1_g. Let F be a nondegenerate,
symmetric, arity n ≥ 3 signature of type 𝔉. Then, there exists u1, . . . , uk ∈ C^3 for k = n − 3
such that connecting u1, . . . , uk to F results in a ternary signature G of type 𝔉. Further, if T
is an orthogonal matrix such that TF is of the defining form, then TG is of the defining form as
well."

**Formalization Note.** Both sentences, for one and the same `G`: the list `us` has length
`n − 3` (natural-number subtraction, with `n ≥ 3` from `IsType`), `G = F.contractMany us` has
arity 3 and type `τ`, and every orthogonal `T` bringing `F` to the defining form of `τ` brings `G`
to it. -/
theorem proposition_9_10 (τ : TractType) (F : Sig 3) (hF : IsType τ F) :
    ∃ us : List (Fin 3 → ℂ), us.length = F.1 - 3 ∧ IsType τ (F.contractMany us) ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℂ, IsOrth3 T → DefForm τ (act T F) →
        DefForm τ (act T (F.contractMany us)) := by sorry

end Holant3Dich
