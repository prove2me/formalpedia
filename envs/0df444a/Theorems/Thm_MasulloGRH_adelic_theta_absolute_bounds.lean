-- Prove2me | Theorems.Thm_MasulloGRH_adelic_theta_absolute_bounds
-- name    : MasulloGRH.adelic_theta_absolute_bounds
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:44:02.692733+00:00
-- url     : https://prove2.me/theorems/716be23c-4c1f-4213-bb5a-fab0340d1197
-- title:
--   Theorem 2.2.3.4, absolute form — $\sum_{\xi\in F^\times}|f(\xi g)|$ and $\sum|\widehat f(\xi g)|$ decay rapidly for $|g|_F\ge1$ and are $O(|g|_F^{-1})$ for $|g|_F\le1$
-- statement:
--   Let $F$ be a number field, $f\in\mathcal S(\mathbb A_F)$ a Schwartz–Bruhat function on the adeles, $\widehat f$ its adelic Fourier transform (standard additive character, Tamagawa measure), and $\Phi_F(f)(g)=\sum_{\xi\in F^\times}f(\xi g)$ its global θ-function on the ideles. Write $|g|_F$ for the idelic norm.
--
--   1. **Regularity.** $f$ is continuous on $\mathbb A_F$; $\widehat f$ is Borel measurable on $\mathbb A_F$; $\Phi_F(f)$ is continuous on $\mathrm{GL}_1(\mathbb A_F)$.
--
--   2. **Absolute sums for $f$.** For every integer $N\ge0$ there is a constant $C$ such that for every idele $g$ the series $\sum_{\xi\in F^\times}|f(\xi g)|$ converges, and
--   $$\sum_{\xi\in F^\times}|f(\xi g)|\le C\,|g|_F^{-N}\quad\text{if }|g|_F\ge1,\qquad
--   \sum_{\xi\in F^\times}|f(\xi g)|\le C\,|g|_F^{-1}\quad\text{if }|g|_F\le1 .$$
--
--   3. **Absolute sums for $\widehat f$.** The same statement holds with $\widehat f$ in place of $f$.
--
--   **Role.** Theorem 2.2.3.4 of the source bounds $|\Phi_F(f)(g)|$, the absolute value of the sum. The proof of Theorem 3.2.2.1(1) needs more: the zeta integral $Z(f,c)=\int_{\mathrm{GL}_1(\mathbb A_F)}f(g)c(g)\,d\mu(g)$ converges absolutely for $\sigma(c)>1$ exactly because $\int_{C_F}\sum_\xi|f(\xi x)|\,|x|_F^{\sigma}\,d\bar\mu(x)<\infty$, and since $|f|$ is not a Schwartz–Bruhat function this does not follow from the bounds on $\Phi_F(f)$. Items 2 and 3 supply this for $f$ and for $\widehat f$ (the latter is needed for $Z(\widehat f,\widehat c)$ in the functional equation). Item 1 gives the measurability of the integrands. The exponent $-1$ for small $|g|_F$ cannot be improved in general: for $f\ge0$ the sum is $\Phi_F(f)(g)\sim|g|_F^{-1}\widehat f(0)$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 2.2.3.4, eqs. (2.2.3.4)–(2.2.3.5), pp. 82–83 (bounds for the θ-function); the absolute convergence is used in Theorem 3.2.2.1(1), pp. 124–127.

import Definitions.Def_MasulloGRH_AdelicTheta

set_option autoImplicit false
namespace MasulloGRH

open NumberField IsDedekindDomain MeasureTheory

theorem adelic_theta_absolute_bounds (F : Type*) [Field F] [NumberField F] (f : AdelicSchwartz F) :
    Continuous f.eval ∧ Measurable (adelicFourier f) ∧ Continuous (adelicTheta f) ∧
    (∀ N : ℕ, ∃ C : ℝ, ∀ g : IdeleGroup F,
      Summable (fun ξ : Fˣ => ‖f.eval (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖) ∧
      (1 ≤ ideleNorm g →
        ∑' ξ : Fˣ, ‖f.eval (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ ≤ C * ideleNorm g ^ (-(N : ℝ))) ∧
      (ideleNorm g ≤ 1 →
        ∑' ξ : Fˣ, ‖f.eval (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ ≤ C * (ideleNorm g)⁻¹)) ∧
    (∀ N : ℕ, ∃ C : ℝ, ∀ g : IdeleGroup F,
      Summable (fun ξ : Fˣ => ‖adelicFourier f (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖) ∧
      (1 ≤ ideleNorm g →
        ∑' ξ : Fˣ, ‖adelicFourier f (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ ≤ C * ideleNorm g ^ (-(N : ℝ))) ∧
      (ideleNorm g ≤ 1 →
        ∑' ξ : Fˣ, ‖adelicFourier f (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ ≤ C * (ideleNorm g)⁻¹)) := by sorry

end MasulloGRH
