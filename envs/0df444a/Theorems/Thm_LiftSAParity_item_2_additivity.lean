-- Prove2me | Theorems.Thm_LiftSAParity_item_2_additivity
-- name    : LiftSAParity.item_2_additivity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:23.589608+00:00
-- url     : https://prove2.me/theorems/1c25239c-1ccf-4c2f-afb4-a5c4414e12de
-- title:
--   Item (2), eqs. (33)–(36) — approximate additivity of $\mu$ under slicing
-- statement:
--   Let $\ell\ge2$, $d\ge4\ell$, $\mathcal D$ a $d$-local distribution for $F$, $\gamma$ stifling inputs for $g$, $r=\lfloor d/2\ell\rfloor$ and $\delta=e^{-d/8\ell^3}$. Let $A$ be a nonempty affine space with $\operatorname{rk}A\le r-1$, $f$ a linear form, $A_b=A\cap\{f=b\}$, and $\Delta_J=\mu_J(A)-\mu_J(A_0)-\mu_J(A_1)$. Then
--   $$|\mu(A)-\mu(A_0)-\mu(A_1)|=\big|\mathop{\mathbb E}_J[\Delta_J]\big|\le\delta. \tag{33}$$
--   If $f$ is non-constant on $A$, moreover
--
--   1. $I(J,A_0)=I(J,A_1)$ for every $J$;
--   2. $\Delta_J=0$ whenever $|I(J,A_0)|<d$ (34)–(35);
--   3. $$\big|\mathop{\mathbb E}_J[\Delta_J]\big|\le\Pr_J\big[|I(J,A_0)|=d\big]\le\exp\Big(-\frac d{16\ell}\Big). \tag{36}$$
--
--   **Formalization Note** The linear form is $f_S$ with support $S$; $\mu(\emptyset)=0$ covers the constant case.
--
--   Differences from the source:
--   - generalization: the standing hypotheses of §4 include F unsatisfiable → F is not assumed unsatisfiable; reason: the argument does not use it; the Lean statement specializes to the printed one
--   - generalization: integers n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 the cube has a single point and the statement is degenerate; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.2, p.16, item (2), eqs. (33)–(36)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsLocalDist
import Definitions.Def_LiftSAParity_IsStiflingInputs
import Definitions.Def_LiftSAParity_lift
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_blocks
import Definitions.Def_LiftSAParity_mu

namespace LiftSAParity

/-- **Item (2) of Lemma 3.4 for µ, eqs. (33)–(36)** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §4.2, p.16). Under the standing
hypotheses of §4 (`ℓ ≥ 2`, `d ≥ 4ℓ`, `D` a `d`-local distribution for `F`, `γ` stifling inputs for
`g`), with `r = ⌊d/2ℓ⌋` and `δ = exp(−d/8ℓ³)`: let `A` be a nonempty affine space with
`rk A ≤ r − 1`, `f` a linear form, `A_b = A ∩ {f = b}` and `∆_J = µ_J(A) − µ_J(A₀) − µ_J(A₁)`. Then
(33) `|µ(A) − µ(A₀) − µ(A₁)| ≤ δ`. If `f` is non-constant on `A`, moreover `I(J, A₀) = I(J, A₁)` for
every `J` (p.16), (34)–(35) `∆_J = 0` whenever `|I(J, A₀)| < d`, and (36)
`|E_J[∆_J]| ≤ Pr_J[|I(J, A₀)| = d] ≤ exp(−d/16ℓ)`.

**Formalization Note** The linear form `f` is `f_S` with support `S`; `slice A S b = A ∩ {f_S = b}`.
`µ(∅) = 0` by definition, which covers the constant case. -/
theorem item_2_additivity {n ℓ d : ℕ} (g : (Fin ℓ → Bool) → Bool) (F : CNF (Fin n))
    (D : (I : Finset (Fin n)) → (I → Bool) → ℝ) (γ : Fin ℓ → Bool → (Fin ℓ → Bool))
    (hℓ : 2 ≤ ℓ) (hd : 4 * ℓ ≤ d) (hD : IsLocalDist F d D) (hγ : IsStiflingInputs g γ)
    (A : Set (Fin n × Fin ℓ → ZMod 2)) (hA : IsAffineSpace A) (hne : A.Nonempty)
    (hcod : codim A ≤ d / (2 * ℓ) - 1) (S : Finset (Fin n × Fin ℓ)) :
    |mu d D γ A - mu d D γ (slice A S 0) - mu d D γ (slice A S 1)| ≤
        Real.exp (-(d : ℝ) / (8 * (ℓ : ℝ) ^ 3)) ∧
    (¬ IsConstOn S A →
      (∀ J : Fin n → Fin ℓ, blocks d J (slice A S 0) = blocks d J (slice A S 1)) ∧
      (∀ J : Fin n → Fin ℓ, (blocks d J (slice A S 0)).card < d →
        muJ d D γ J A - muJ d D γ J (slice A S 0) - muJ d D γ J (slice A S 1) = 0) ∧
      |expJ (fun J => muJ d D γ J A - muJ d D γ J (slice A S 0) - muJ d D γ J (slice A S 1))| ≤
        probJ (fun J : Fin n → Fin ℓ => (blocks d J (slice A S 0)).card = d) ∧
      probJ (fun J : Fin n → Fin ℓ => (blocks d J (slice A S 0)).card = d) ≤
        Real.exp (-(d : ℝ) / (16 * (ℓ : ℝ)))) := by sorry

end LiftSAParity
