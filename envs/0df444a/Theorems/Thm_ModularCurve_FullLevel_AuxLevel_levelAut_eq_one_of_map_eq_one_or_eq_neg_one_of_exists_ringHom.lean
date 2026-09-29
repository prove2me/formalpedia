-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom
-- name    : ModularCurve.FullLevel.AuxLevel.levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/112ab275-1160-5fb2-8e56-c2ae46a6d8b1
-- title:
--   Level automorphism attached to γ ≡ ± 1 (mod qℓ) is trivial
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M' \ge 1$ with $q \nmid M'$, and let $\ell$ be a prime with $\ell \ge 3$, $\ell \neq q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic $0$, let $\xi \in L$ be a primitive $(q\ell)$-th root of unity, and assume there is a ring homomorphism $\iota_0 : L \to \mathbb{C}$ with $\iota_0(\xi) = \exp(2\pi i/(q\ell))$. Put $N_0 = (q\ell)^2 M'$ and let $H \le (\mathbb{Z}/N_0)^\times$ be the kernel of reduction $(\mathbb{Z}/N_0)^\times \to (\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$; write $\Gamma_H \le \mathrm{SL}_2(\mathbb{Z})$ for the image of the preimage of $H$ under the lower-right-entry map on $\Gamma_0(N_0)$. Let $K$ be the intermediate field of $L((t))/L$ generated over $L$ by the coefficientwise image, under $\mathbb{Q} \to L$, of the $q$-expansion function field of $\Gamma_H$ inside $\mathbb{Q}((t))$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and satisfy $\gamma \equiv 1$ or $\gamma \equiv -1$ modulo $q\ell$, and let $\tau$ be an $L$-algebra automorphism of $K$ which is a level automorphism at $\gamma^{-1}$ in the following sense: for every $k \in \mathbb{Z}$, all modular forms $f, g$ of weight $k$ for $\Gamma_H$ (regarded inside $\mathrm{GL}_2(\mathbb{R})$), all integral power series $p_f, p_g$ whose images in $\mathbb{C}[[t]]$ are the width-$1$ $q$-expansions of $f$ and $g$, with the Laurent series $P_g$ attached to $p_g$ over $\mathbb{Q}$ nonzero, every $x \in K$ mapping to the coefficientwise image in $L((t))$ of $P_f/P_g$, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$, one has $$\iota_*(\tau x) \cdot \big(q\text{-expansion of } g \mid_k \gamma^{-1,\sharp}\big) = q\text{-expansion of } f \mid_k \gamma^{-1,\sharp},$$ where for $\delta = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$ the matrix $\delta^\sharp \in \mathrm{GL}_2(\mathbb{R})$ is $\begin{pmatrix} a & b/(q\ell) \\ (q\ell)c & d\end{pmatrix}$. Then $\tau = 1$.
--
--   This is the triviality half of the reciprocity description of automorphisms of the modular function field: an automorphism attached to an element of $\Gamma_0(M')$ that is $\pm 1$ modulo the full level $q\ell$ acts trivially, because $(\gamma^{-1})^\sharp$ fixes all forms on $\Gamma_H$ up to the sign $(-1)^k$, which cancels in ratios of forms of equal weight. It is used in the computation of the group of level automorphisms of $K/L$, in particular in identifying its cardinality with that of $\mathrm{SL}_2(\mathbb{Z}/q\ell)$ and in the identification of the Galois action on Drinfeld-style fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (hγ1 : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) γ = 1 ∨
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) γ = -1)
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ) :
    τ = 1 := by sorry
