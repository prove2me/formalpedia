-- Prove2me | Theorems.Thm_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound
-- name    : NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/bca66f65-dec5-5809-ac42-fc9164f7024b
-- title:
--   Adelic bound for dilation-dominated equivariant families on A_F^×
-- statement:
--   Let $F$ be a number field and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the unit-group homomorphism obtained from the module character `distribHaarChar` of the adele ring by composing with the inclusion $\mathbb{R}_{\ge 0}\hookrightarrow\mathbb{R}$. The assertion is: for every compact set $Y$ of ideles units there is a compact set $U'$ of idele units such that for all $k, N \in \mathbb{N}$, every fractional ideal $I$ of $\mathcal{O}_F$ in $F$ and all reals $\sigma_1,\sigma_2,c'$ with $c' > 0$, there is $N_d \in \mathbb{N}$, and then for every real $c$ there is a real $M$, with the following property. Let $G$ assign a real number $G(\xi,y)$ to each nonzero $\xi \in F$ and each idele unit $y$, and let $\sigma$ satisfy $\sigma_1 \le \sigma \le \sigma_2$; assume $G \ge 0$; assume the equivariance $G(\xi, \eta y) = G(\xi\eta, y)$ for $\eta \in F^\times$ embedded diagonally; and assume that for every $u \in U'$, every $r > 0$ and every idele unit $z$ whose finite part is $1$ and all of whose archimedean components equal $r$ (under the embeddings of the completions into $\mathbb{C}$), one has $G(\xi, zu) = 0$ unless $\xi \in I$, together with the dilation bound $$G(\xi,zu) \le c\, r^{[F:\mathbb{Q}](1/2-\sigma)} \max(1,|N_{F/\mathbb{Q}}(\xi)|)^{k} \prod_{w \text{ real}} (1+r|\xi_w|)^{-N_d} \prod_{w \text{ complex}} (1+r\|\xi_w\|)^{-2N_d},$$ the archimedean coordinates $\xi_w$ being those of the mixed embedding of $\xi$. Then for all idele units $y_1, y_0$ with $y_0 \in Y$ and $\alpha(y_1) \ge c'$, the family $\xi \mapsto G(\xi, y_1y_0)$ over nonzero $\xi \in F$ is summable and $\sum_{\xi \ne 0} G(\xi, y_1 y_0) \le M\,\alpha(y_1)^{-N}$. Note the order of quantification: $U'$ depends only on $Y$, the integer $N_d$ is produced before $c$, and $M$ depends on $c$ as well as on the earlier data.
--
--   This is the GL(1) reduction-theory and lattice-counting step in the style of Tate's thesis: compactness of the norm-one idele class group lets an arbitrary idele be written as a principal unit times an archimedean dilation times an element of a fixed compact set, after which the decay hypothesis is summed over the nonzero elements of a fractional ideal. It isolates the adelic bookkeeping used in the bounds on analytically continued Whittaker coefficients of Bruhat–Eisenstein series, and it cites the decomposition of idele units over a compact set, the lattice-sum estimate for fractional ideals under the mixed embedding, and the triviality of the module character on principal ideles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound.lean

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

theorem NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound
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
              (∀ u ∈ U', ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r →
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
