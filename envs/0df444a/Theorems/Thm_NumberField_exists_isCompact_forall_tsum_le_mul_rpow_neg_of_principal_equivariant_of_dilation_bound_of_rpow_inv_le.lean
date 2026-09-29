-- Prove2me | Theorems.Thm_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le
-- name    : NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/c745cbc2-e74f-5a7f-af93-3f6f12c14e67
-- title:
--   Adelic decay of principal-equivariant families with archimedean dilation bound
-- statement:
--   Let $F$ be a number field and let $\alpha\colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the homomorphism on the unit group of the adele ring obtained from the module `distribHaarChar` of the adele ring by composing with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units. The assertion is that for every compact set $Y$ of ideles there is a compact set $U'$ of ideles such that, for every $k,N \in \mathbb{N}$, every fractional ideal $I$ of $\mathcal{O}_F$ in $F$ and all reals $\sigma_1,\sigma_2,c'$ with $c'>0$, there is $N_d \in \mathbb{N}$, and for each real $c$ a real $M$, with the following property. Let $G$ assign a real number to each pair consisting of a nonzero $\xi \in F$ and an idele, and let $\sigma_1 \le \sigma \le \sigma_2$. Assume: $G$ is nonnegative; $G$ is equivariant for the diagonal image of $F^\times$, that is $G(\xi, \eta y) = G(\xi\eta, y)$ for $\eta \in F^\times$; and for every $u \in U'$, every idele $z$ whose finite part is $1$ and all of whose infinite components map to the real number $r$ under the embedding of the completion at $w$ into $\mathbb{C}$, with $r \ge c'^{1/[F:\mathbb{Q}]}$, and every nonzero $\xi$: $G(\xi, zu) = 0$ unless $\xi \in I$, and
--   $$G(\xi,zu) \le c\, r^{[F:\mathbb{Q}](1/2-\sigma)} \max\bigl(1,|N_{F/\mathbb{Q}}(\xi)|\bigr)^{k} \prod_{w \text{ real}} (1+r|\xi_w|)^{-N_d} \prod_{w \text{ complex}} (1+r\|\xi_w\|)^{-2N_d},$$
--   the archimedean components being those of the mixed embedding of $\xi$. Then for all ideles $y_1,y_0$ with $y_0 \in Y$ and $\alpha(y_1) \ge c'$, the family $\xi \mapsto G(\xi, y_1y_0)$ over nonzero $\xi \in F$ is summable and
--   $$\sum_{\xi \ne 0} G(\xi, y_1 y_0) \le M\, \alpha(y_1)^{-N}.$$
--
--   This is the adelic reduction-theory step for $\mathrm{GL}_1$ in the style of Tate's thesis: compactness of the norm-one idele class group allows an arbitrary idele to be replaced by an archimedean dilation times an element of a fixed compact set, after which a lattice-point estimate over a fractional ideal converts the pointwise dilation bound into decay of the full sum in the idele norm. It serves the packaging of Whittaker coefficients of Bruhat–Eisenstein series, where the relevant pointwise bounds are available beyond a threshold in the dilation parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal

open scoped Classical in

theorem NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound_of_rpow_inv_le
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (Y : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact Y →
      ∃ U' : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact U' ∧
        ∀ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (σ₁ σ₂ c' : ℝ) (N : ℕ), 0 < c' →
          ∃ Nd : ℕ, ∀ c : ℝ, ∃ M : ℝ,
            ∀ (G : {ξ : F // ξ ≠ 0} → (AdeleRing (𝓞 F) F)ˣ → ℝ) (σ : ℝ), σ₁ ≤ σ → σ ≤ σ₂ →
              (∀ ξ y, 0 ≤ G ξ y) →
              (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (y : (AdeleRing (𝓞 F) F)ˣ),
                G ξ (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
                  = G ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ y) →
              (∀ u ∈ U', ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), c' ^ ((Module.finrank ℚ F : ℝ)⁻¹) ≤ r →
                (z : AdeleRing (𝓞 F) F).2 = 1 →
                (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
                ∀ ξ : {ξ : F // ξ ≠ 0},
                  ((ξ : F) ∉ I → G ξ (z * u) = 0) ∧
                  G ξ (z * u) ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - σ)) *
                    (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                    (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(Nd : ℝ))) *
                    ∏ w : {w : InfinitePlace F // w.IsComplex},
                      (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * Nd : ℝ))) →
              ∀ (y₁ y₀ : (AdeleRing (𝓞 F) F)ˣ), y₀ ∈ Y → c' ≤ ((α y₁ : ℝˣ) : ℝ) →
                Summable (fun ξ : {ξ : F // ξ ≠ 0} => G ξ (y₁ * y₀)) ∧
                ∑' ξ : {ξ : F // ξ ≠ 0}, G ξ (y₁ * y₀) ≤ M * ((α y₁ : ℝˣ) : ℝ) ^ (-(N : ℝ)) := by sorry
