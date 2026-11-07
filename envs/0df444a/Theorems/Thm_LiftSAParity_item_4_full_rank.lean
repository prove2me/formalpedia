-- Prove2me | Theorems.Thm_LiftSAParity_item_4_full_rank
-- name    : LiftSAParity.item_4_full_rank
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:12.794861+00:00
-- url     : https://prove2.me/theorems/371bca5b-f387-4ff3-9816-ff1ef3e781b5
-- title:
--   Items (1) and (4), eqs. (27)–(29) — $\mu(\text{cube})=1$ and $\mu(A)\le\delta$ when $\operatorname{rk}A=r$
-- statement:
--   Let $\ell\ge2$, $d\ge4\ell$, $\mathcal D$ a $d$-local distribution for $F$, $\gamma$ stifling inputs for $g$, $r=\lfloor d/2\ell\rfloor$ and $\delta=e^{-d/8\ell^3}$. Then $\mu(\{0,1\}^{n\times\ell})=1$ (item (1)), and for every nonempty affine space $A$ with $\operatorname{rk}A=r$ (item (4)):
--   $$|\mu(A)|=\mu(A)=\mathop{\mathbb E}_J[\mu_J(A)]\le\mathop{\mathbb E}_J\big[2^{-|I^\star(J,A)|}\big]\le\Big(1-\frac1{2\ell}\Big)^{r/\ell}\le\exp\Big(-\frac r{2\ell^2}\Big)\le\delta. \tag{29}$$
--
--   The middle inequality is (28): each iteration of the block selection is a pivot with conditional probability at least $1/\ell$ (27), and at least $r/\ell$ blocks are processed.
--
--   **Formalization Note** $r$ is natural-number floor division `d / (2 * ℓ)`; the exponent $r/\ell$ is real. $|\mu(A)|=\mu(A)$ is stated as $0\le\mu(A)$, and $\mu(A)=\mathbb E_J[\mu_J(A)]$ is the definition of $\mu$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses of §4 include F unsatisfiable → F is not assumed unsatisfiable; reason: the argument does not use it; the Lean statement specializes to the printed one
--   - generalization: integers n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 the cube has a single point and the statement is degenerate; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.2, pp.14–15, items (1) and (4), eqs. (27)–(29)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsLocalDist
import Definitions.Def_LiftSAParity_IsStiflingInputs
import Definitions.Def_LiftSAParity_lift
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_blocks
import Definitions.Def_LiftSAParity_mu

namespace LiftSAParity

/-- **Items (1) and (4) of Lemma 3.4 for µ, eqs. (27)–(29)** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §4.2, pp.14–15). Under the
standing hypotheses of §4 (`ℓ ≥ 2`, `d ≥ 4ℓ`, `D` a `d`-local distribution for `F`, `γ` stifling
inputs for `g`), with `r = ⌊d/2ℓ⌋` and `δ = exp(−d/8ℓ³)`:
item (1), `µ({0,1}^{n×ℓ}) = 1`; and item (4), display (29): for every nonempty affine `A` with
`rk A = r`,
`|µ(A)| = µ(A) = E_J[µ_J(A)] ≤ E_J[2^{−|I⋆(J,A)|}] ≤ (1 − 1/2ℓ)^{r/ℓ} ≤ exp(−r/2ℓ²) ≤ δ`.

**Formalization Note** `r = d / (2 * ℓ)` is natural-number (floor) division; the exponent `r/ℓ` is
real (`Real.rpow`). `|µ(A)| = µ(A)` is the conjunct `0 ≤ µ(A)`; `µ(A) = E_J[µ_J(A)]` is the
definition of `mu`. -/
theorem item_4_full_rank {n ℓ d : ℕ} (g : (Fin ℓ → Bool) → Bool) (F : CNF (Fin n))
    (D : (I : Finset (Fin n)) → (I → Bool) → ℝ) (γ : Fin ℓ → Bool → (Fin ℓ → Bool))
    (hℓ : 2 ≤ ℓ) (hd : 4 * ℓ ≤ d) (hD : IsLocalDist F d D) (hγ : IsStiflingInputs g γ) :
    mu d D γ Set.univ = 1 ∧
    ∀ A : Set (Fin n × Fin ℓ → ZMod 2), IsAffineSpace A → A.Nonempty → codim A = d / (2 * ℓ) →
      0 ≤ mu d D γ A ∧
      mu d D γ A ≤ expJ (fun J => (1 / 2 : ℝ) ^ (pivots d J A).card) ∧
      expJ (fun J => (1 / 2 : ℝ) ^ (pivots d J A).card) ≤
        (1 - 1 / (2 * (ℓ : ℝ))) ^ (((d / (2 * ℓ) : ℕ) : ℝ) / ℓ) ∧
      (1 - 1 / (2 * (ℓ : ℝ))) ^ (((d / (2 * ℓ) : ℕ) : ℝ) / ℓ) ≤
        Real.exp (-((d / (2 * ℓ) : ℕ) : ℝ) / (2 * (ℓ : ℝ) ^ 2)) ∧
      Real.exp (-((d / (2 * ℓ) : ℕ) : ℝ) / (2 * (ℓ : ℝ) ^ 2)) ≤
        Real.exp (-(d : ℝ) / (8 * (ℓ : ℝ) ^ 3)) := by sorry

end LiftSAParity
