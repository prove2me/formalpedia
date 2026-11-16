-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_algebraic_immunity_mod3_lower_bound
-- name    : GoldreichAffine.Exponential.Supplement.algebraic_immunity_mod3_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:53:24.443191+00:00
-- url     : https://prove2.me/theorems/7a437b4d-4db4-4c8f-98eb-5712a1803e43
-- title:
--   Lemma 10 — algebraic immunity ≥ ⌊(d+1)/3⌋ for symmetric predicates fixed on two residues mod 3
-- statement:
--   Let $P_d$ be a symmetric Boolean function on $d\ge6$ inputs. Suppose there are distinct residues $\alpha,\beta\in\{0,1,2\}$ such that
--
--   $$P_d(z)=0\ \text{ if }\|z\|\equiv\alpha\pmod3,\qquad P_d(z)=1\ \text{ if }\|z\|\equiv\beta\pmod3 .$$
--
--   Then
--
--   $$\mathrm{AI}(P_d)\ge\Big\lfloor\frac{d+1}3\Big\rfloor .$$
--
--   Theorem 5 is a direct application of this bound to the residuals of MOD12.
--
--   Differences from the source:
--   - encoding: ⌊(d+1)/3⌋ → (d + 1) / 3 in ℕ; reason: natural-number division is the floor
--   - encoding: ‖z‖ ≡ α (mod 3), α ∈ {0,1,2} → weight z % 3 = α, α < 3; reason: same condition
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 33 (PDF p. 34), Lemma 10; proof pp. 33–34 (PDF pp. 34–35)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Algebraic
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Lemma 10, printed p.33 / PDF p.34: AI(P_d) ≥ ⌊(d+1)/3⌋ (natural division is the floor). -/
theorem algebraic_immunity_mod3_lower_bound (d : ℕ) (P : Predicate d) (hsym : IsSymmetric P)
    (hd : 6 ≤ d) (α β : ℕ) (hα : α < 3) (hβ : β < 3) (hαβ : α ≠ β)
    (h0 : ∀ z : Word d, weight z % 3 = α → P z = false)
    (h1 : ∀ z : Word d, weight z % 3 = β → P z = true) :
    (d + 1) / 3 ≤ algebraicImmunity P := by sorry

end GoldreichAffine.Exponential.Supplement
