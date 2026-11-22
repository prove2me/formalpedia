-- Prove2me | Theorems.Thm_MasulloGRH_tamagawa_measures_wellDefined
-- name    : MasulloGRH.tamagawa_measures_wellDefined
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:31:44.621141+00:00
-- url     : https://prove2.me/theorems/f8192754-eb09-4e6d-ac75-d98c426339a7
-- title:
--   Definition A.3.2.1 — the Tamagawa measures on $C_F$ and $\mathrm{GL}_1(\mathbb A_F)$ are well defined: Haar, unique, unfolding, norm push-forward
-- statement:
--   Let $F$ be a number field, $C_F=\mathrm{GL}_1(\mathbb A_F)/F^\times$ its idele class group, $|\cdot|_F$ the idelic norm, and
--   $$V=\mu_1(C_F^1)=\frac{2^{r_1}(2\pi)^{r_2}h_FR_F}{|d_F|^{1/2}w_F}=\operatorname{Res}_{s=1}\zeta_F(s)$$
--   the volume of (A.3.2.1).
--
--   Definition A.3.2.1 of the source speaks of *the unique Haar measure* $\mu$ on $\mathrm{GL}_1(\mathbb A_F)$ which, with the counting measure on $F^\times$, induces a Haar measure $\bar\mu$ on $C_F$ that together with $dt/t$ on $\mathbb R_{>0}\simeq C_F/C_F^1$ gives $C_F^1$ the volume $V$. The formal definitions `tamagawaIdeleClass F` ($\bar\mu$) and `tamagawaIdele F` ($\mu$) choose a measure with the defining properties **if one exists** and are the zero measure otherwise. This theorem proves that such measures exist and are unique, so the formal objects are the ones the source intends, and it records the integration formulas that follow.
--
--   1. **The measure on $C_F$.** $\bar\mu$ is a Haar measure on $C_F$ with
--   $$\bar\mu\bigl(\{x\in C_F:\ 1\le |x|_F<e\}\bigr)=V,$$
--   and it is the only Haar measure on $C_F$ with this normalization.
--
--   2. **The measure on the ideles.** $\mu$ is a Haar measure on $\mathrm{GL}_1(\mathbb A_F)$. For every Borel set $D$ of ideles on which the projection $\pi\colon \mathrm{GL}_1(\mathbb A_F)\to C_F$ is injective, $\mu(D)=\bar\mu(\pi(D))$. It is the only measure on the ideles with this property.
--
--   3. **Unfolding.** For every Borel function $\varphi\ge 0$ on the ideles,
--   $$\int_{\mathrm{GL}_1(\mathbb A_F)}\varphi(g)\,d\mu(g)=\int_{C_F}\ \sum_{\xi\in F^\times}\varphi(\xi x)\,d\bar\mu(x),$$
--   and the same identity holds for every $\mu$-integrable complex-valued $\varphi$. In the formal statement the class $x$ is represented by the idele `x.out`; the inner sum does not depend on the representative.
--
--   4. **Push-forward under the norm.** The image of $\bar\mu$ under $x\mapsto\log|x|_F$ is $V$ times Lebesgue measure on $\mathbb R$. Equivalently, the image of $\bar\mu$ under $|\cdot|_F$ is $V\,dt/t$ on $\mathbb R_{>0}$.
--
--   5. **Inversion.** $\bar\mu$ is invariant under $x\mapsto x^{-1}$.
--
--   **Role.** Every statement about the global zeta integral $Z(f,c)=\int f(g)c(g)\,d\mu(g)$ and the Mellin transform $L(f,c)=\int_{C_F}\Phi_F(f)(x)c(x)\,d\bar\mu(x)$ of Theorem 3.2.2.1 depends on these measures being non-degenerate. Items 3–5 are the measure-theoretic inputs of Tate's computation: unfolding $Z$ into $L$, evaluating the polar terms $\int_{|x|<1}|x|^{s}\,d\bar\mu=V/s$, and the substitution $x\mapsto x^{-1}$ in the functional equation.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, §A.3.2, Definition A.3.2.1 and eq. (A.3.2.1), pp. 559–560; the measures are used in Theorem 3.2.2.1, eqs. (3.2.2.1) and (3.2.2.3), pp. 124–125.

import Definitions.Def_MasulloGRH_ZetaIntegrals

set_option autoImplicit false
namespace MasulloGRH

open NumberField IsDedekindDomain MeasureTheory

theorem tamagawa_measures_wellDefined (F : Type*) [Field F] [NumberField F] :
    ((tamagawaIdeleClass F).IsHaarMeasure ∧
      tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
          {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
        ENNReal.ofReal (tamagawaClassVolume F) ∧
      ∀ μ' : Measure (IdeleClassGroup F), μ'.IsHaarMeasure →
        μ' ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) ''
          {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}) =
          ENNReal.ofReal (tamagawaClassVolume F) → μ' = tamagawaIdeleClass F) ∧
    ((tamagawaIdele F).IsHaarMeasure ∧
      (∀ D : Set (IdeleGroup F), MeasurableSet D →
        Set.InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) D →
        tamagawaIdele F D =
          tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' D)) ∧
      ∀ μ' : Measure (IdeleGroup F),
        (∀ D : Set (IdeleGroup F), MeasurableSet D →
          Set.InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) D →
          μ' D =
            tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' D)) →
        μ' = tamagawaIdele F) ∧
    (∀ φ : IdeleGroup F → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂(tamagawaIdele F) =
        ∫⁻ x : IdeleClassGroup F, ∑' ξ : Fˣ, φ (principalIdele F ξ * x.out)
          ∂(tamagawaIdeleClass F)) ∧
    (∀ φ : IdeleGroup F → ℂ, Integrable φ (tamagawaIdele F) →
      ∫ g, φ g ∂(tamagawaIdele F) =
        ∫ x : IdeleClassGroup F, ∑' ξ : Fˣ, φ (principalIdele F ξ * x.out)
          ∂(tamagawaIdeleClass F)) ∧
    Measure.map (fun x : IdeleClassGroup F => Real.log (ideleNorm x.out)) (tamagawaIdeleClass F) =
      ENNReal.ofReal (tamagawaClassVolume F) • (volume : Measure ℝ) ∧
    Measure.map (fun x : IdeleClassGroup F => x⁻¹) (tamagawaIdeleClass F) =
      tamagawaIdeleClass F := by sorry

end MasulloGRH
