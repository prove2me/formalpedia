-- Prove2me | Theorems.Thm_LiftSAParity_item_3_clause
-- name    : LiftSAParity.item_3_clause
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:57.317342+00:00
-- url     : https://prove2.me/theorems/e481083d-aded-40b0-a158-37598f7fd9af
-- title:
--   Item (3), eqs. (31)–(32) — $\mu(A_C\cap A)\le\delta$
-- statement:
--   Let $\ell\ge2$, $d\ge4\ell$, $\mathcal D$ a $d$-local distribution for $F$, $\gamma$ stifling inputs for $g$, $r=\lfloor d/2\ell\rfloor$ and $\delta=e^{-d/8\ell^3}$. Let $C$ be a clause of $F\circ g$ and $B=A_C\cap A$ a nonempty affine space of rank at most $r$. Then
--
--   1. $\mu_J(B)=0$ for every $J$ with $|I(J,B)|<d$ (31);
--   2. $$|\mu(B)|=\mu(B)\le\Pr_J\big[|I(J,B)|=d\big]\le\exp(-d/16\ell)\le\delta. \tag{32}$$
--
--   Off the cutoff the selected blocks contain every block of $C$, the gadget outputs on them follow the satisfying local distribution, and so the sample never falsifies $C$.
--
--   **Formalization Note** "$B=A_C\cap A$ for an affine $A$" is written as "$B$ affine and $B\subseteq A_C$".
--
--   Differences from the source:
--   - encoding: B = A_C ∩ A for an affine space A → B affine and B ⊆ A_C; reason: equivalent: take A = B; conversely A_C ∩ A is affine
--   - encoding: B may be empty ("If B is empty, its measure is zero") → B nonempty; reason: rank is defined only for nonempty spaces, and µ(∅) = 0 holds by the definition of `mu`, so the empty case is definitional
--   - generalization: the standing hypotheses of §4 include F unsatisfiable → F is not assumed unsatisfiable; reason: the argument does not use it; the Lean statement specializes to the printed one
--   - generalization: integers n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 the cube has a single point and the statement is degenerate; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.2, p.15, item (3), eqs. (31)–(32)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsLocalDist
import Definitions.Def_LiftSAParity_IsStiflingInputs
import Definitions.Def_LiftSAParity_lift
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_blocks
import Definitions.Def_LiftSAParity_mu

namespace LiftSAParity

/-- **Item (3) of Lemma 3.4 for µ, eqs. (31)–(32)** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §4.2, p.15). Under the standing
hypotheses of §4 (`ℓ ≥ 2`, `d ≥ 4ℓ`, `D` a `d`-local distribution for `F`, `γ` stifling inputs for
`g`), with `r = ⌊d/2ℓ⌋` and `δ = exp(−d/8ℓ³)`: let `C` be a clause of `F ∘ g` and `B = A_C ∩ A` a
nonempty affine space of rank at most `r`. Then (31) `µ_J(B) = 0` for every `J` with
`|I(J, B)| < d`, and (32) `|µ(B)| = µ(B) ≤ Pr_J[|I(J, B)| = d] ≤ exp(−d/16ℓ) ≤ δ`.

**Formalization Note** "`B = A_C ∩ A` for an affine `A`" is written as "`B` affine and
`B ⊆ A_C`" (take `A = B`; conversely `A_C ∩ A` is affine when `A` is). -/
theorem item_3_clause {n ℓ d : ℕ} (g : (Fin ℓ → Bool) → Bool) (F : CNF (Fin n))
    (D : (I : Finset (Fin n)) → (I → Bool) → ℝ) (γ : Fin ℓ → Bool → (Fin ℓ → Bool))
    (hℓ : 2 ≤ ℓ) (hd : 4 * ℓ ≤ d) (hD : IsLocalDist F d D) (hγ : IsStiflingInputs g γ)
    (C : Clause (Fin n × Fin ℓ)) (hC : C ∈ lift F g) (B : Set (Fin n × Fin ℓ → ZMod 2))
    (hB : IsAffineSpace B) (hne : B.Nonempty) (hBC : B ⊆ falsifySpace C)
    (hcod : codim B ≤ d / (2 * ℓ)) :
    (∀ J : Fin n → Fin ℓ, (blocks d J B).card < d → muJ d D γ J B = 0) ∧
    0 ≤ mu d D γ B ∧
    mu d D γ B ≤ probJ (fun J : Fin n → Fin ℓ => (blocks d J B).card = d) ∧
    probJ (fun J : Fin n → Fin ℓ => (blocks d J B).card = d) ≤
      Real.exp (-(d : ℝ) / (16 * (ℓ : ℝ))) ∧
    Real.exp (-(d : ℝ) / (16 * (ℓ : ℝ))) ≤ Real.exp (-(d : ℝ) / (8 * (ℓ : ℝ) ^ 3)) := by sorry

end LiftSAParity
