-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv
-- name    : ModularCurve.FullLevel.exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/7850ef7a-f4bb-549c-9256-51f83332b7e5
-- title:
--   Coefficientwise conjugation preserves level automorphisms
-- statement:
--   Let $L$ be a field of characteristic zero, $n, m, N_0$ natural numbers with $m \neq 0$, $\zeta \in L$, $H$ a subgroup of $(\mathbb{Z}/N_0)^{\times}$, $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, and $K$ an intermediate field of $L \subseteq L((q)) =$ `LaurentSeries L`. Let $\sigma_L$ be a ring automorphism of $L$ and $\tau_c$ a ring automorphism of $K$ acting coefficientwise through $\sigma_L$, i.e. for every $x \in K$ the Laurent series underlying $\tau_c x$ is obtained from that of $x$ by applying $\sigma_L$ to each coefficient ([`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16)). Let $\sigma$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt L n ζ m N₀ H γ K σ`: for every weight $k \in \mathbb{Z}$, every pair $f, g$ of modular forms of weight $k$ for the image of $\Gamma_H(N_0)$ in $\mathrm{GL}_2(\mathbb{R})$, every pair $p_f, p_g$ of integral power series that are the $q$-expansions at $1$ of $f$ and of $g$ with $p_g \neq 0$ over $\mathbb{Q}$, every $x \in K$ whose Laurent series is the image under $\mathbb{Q} \to L$ of $p_f/p_g$, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/n}$, one has $\iota_*(\sigma x)\cdot q\text{-exp}_1(g \mid_k \nu_m(\gamma)) = q\text{-exp}_1(f \mid_k \nu_m(\gamma))$, where $\nu_m(\gamma) = \begin{pmatrix} a & b/m \\ mc & d\end{pmatrix}$ for $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$ (`conjElemN`). The conclusion: there exists an $L$-algebra automorphism $\sigma'$ of $K$ satisfying the same predicate with $\zeta$ replaced by $\sigma_L(\zeta)$, and with $\sigma' x = \tau_c(\sigma(\tau_c^{-1} x))$ for all $x \in K$.
--
--   This is the statement that the group of automorphisms of $K$ cut out by the level conditions at $\gamma$ is normalised by coefficientwise automorphisms, the root of unity $\zeta$ being transported by $\sigma_L$; it is the algebraic shadow of the action of field automorphisms of the constants on $q$-expansions of modular functions. It is used in the construction and stability arguments for the rigid charts of the full-level modular curves, for instance when an inertia element restricted to the constants is extended coefficientwise to the level field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ζ : L) (m : ℕ) [NeZero m]
    (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (K : IntermediateField L (LaurentSeries L))
    (σL : L ≃+* L) (τc : ↥K ≃+* ↥K)
    (hτc : ∀ x : ↥K, ((τc x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L))
    (σ : ↥K ≃ₐ[L] ↥K) (hσ : ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H γ K σ) :
    ∃ σ' : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L n (σL ζ) m N₀ H γ K σ' ∧
      ∀ x : ↥K, σ' x = τc (σ (τc.symm x)) := by sorry
