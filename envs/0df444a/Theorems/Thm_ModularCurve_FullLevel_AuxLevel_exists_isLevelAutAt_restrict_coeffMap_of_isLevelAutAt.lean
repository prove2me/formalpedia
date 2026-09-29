-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt
-- name    : ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/bcbf5321-bafe-577c-ad96-071f6b0ba3ec
-- title:
--   Restricting level automorphisms along a cyclotomic coefficient map
-- statement:
--   Fix primes $q \ge 5$ and $\ell \ge 3$ with $\ell \neq q$, and a nonzero natural number $M'$ divisible by neither $q$ nor $\ell$. Let $L_0$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\xi_0 \in L_0$ be a primitive $q\ell$-th root of unity, let $L$ be a field of characteristic zero and $\iota_0 : L_0 \to L$ a ring homomorphism, and assume there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\iota_0 \xi_0) = \exp(2\pi i/(q\ell))$. Put $N_0 = (q\ell)^2 M'$ and let $H =$ [`ModularCurve.FullLevel.levelH (q * ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22) be the kernel of the reduction map $(\mathbb{Z}/N_0)^{\times} \to (\mathbb{Z}/q\ell)^{\times}$. Let $K_0 \subseteq L_0((\mathsf{q}))$ and $K \subseteq L((\mathsf{q}))$ be the intermediate fields obtained by [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L_0$, respectively $L$, by the coefficientwise image of the field [`ModularCurve.xHFunctionField N₀ H`](def/ModularCurve_XH.html#L79) of $\mathsf{q}$-expansions attached to $\Gamma_H(N_0)$ inside $\mathbb{Q}((\mathsf{q}))$. The conclusion has two parts. First, the coefficientwise ring homomorphism [`ModularCurve.coeffMap ι₀`](def/ModularCurve_LaurentCoeff.html#L16) carries every element of $K_0$ into $K$. Second, for every $\gamma \in SL_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ satisfying `IsLevelAutAt` for the data $(q\ell, \iota_0\xi_0, q\ell, N_0, H, \gamma^{-1})$, there is an $L_0$-algebra automorphism $\tau_0$ of $K_0$ satisfying `IsLevelAutAt` for the corresponding data $(q\ell, \xi_0, q\ell, N_0, H, \gamma^{-1})$ over $L_0$, such that for every $x \in K_0$ (and every witness that $\mathrm{coeffMap}\,\iota_0(x) \in K$) one has $\tau(\mathrm{coeffMap}\,\iota_0(x)) = \mathrm{coeffMap}\,\iota_0(\tau_0 x)$ as Laurent series over $L$. Here the predicate `IsLevelAutAt L n ζ m N₀ H δ K τ` asserts: whenever $f, g$ are modular forms of some weight $k$ for the subgroup of $GL_2(\mathbb{R})$ attached to $\Gamma_H(N_0)$ whose $\mathsf{q}$-expansions at $1$ come from integral power series $p_f, p_g$, with the series of $p_g$ over $\mathbb{Q}$ nonzero, and $x \in K$ is the image under the coefficient embedding of $\mathbb{Q}((\mathsf{q}))$ of the ratio of these series, then for every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota\zeta = \exp(2\pi i/n)$ the complex Laurent series $\mathrm{coeffMap}\,\iota(\tau x)$ times the $\mathsf{q}$-expansion of $g \mid_k \mathrm{conjElemN}\, m\, \delta$ equals the $\mathsf{q}$-expansion of $f \mid_k \mathrm{conjElemN}\, m\, \delta$, where for $\delta = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$ the matrix $\mathrm{conjElemN}\, m\, \delta$ is $\begin{pmatrix} a & b/m \\ mc & d \end{pmatrix}$.
--
--   In the classical language this is the compatibility of Shimura's automorphisms of modular function fields with enlargement of the field of coefficients: a level automorphism attached to $\gamma^{-1}$ over the large field $L$ is the coefficientwise extension of one over the cyclotomic field $L_0 = \mathbb{Q}(\zeta_{q\ell})$. Only the restriction direction is asserted; existence over $L_0$ comes from [`ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom), and the result is used in the construction of the Galois action on completions of stalks of the Drinfeld charts of the auxiliary full-level curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (L : Type) [Field L] [CharZero L] (ι₀ : L₀ →+* L)
    (hι : ∃ ι : L →+* ℂ, ι (ι₀ ξ₀) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :

    (∀ x : ↥K₀, ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K) ∧

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) (ι₀ ξ₀) (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∃ τ₀ : ↥K₀ ≃ₐ[L₀] ↥K₀,
          ModularCurve.FullLevel.IsLevelAutAt L₀ (q * ℓ) ξ₀ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K₀ τ₀ ∧
          ∀ (x : ↥K₀) (hx : ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K),
            ((τ ⟨_, hx⟩ : ↥K) : LaurentSeries L) = ModularCurve.coeffMap ι₀ ((τ₀ x : ↥K₀) : LaurentSeries L₀)) := by sorry
