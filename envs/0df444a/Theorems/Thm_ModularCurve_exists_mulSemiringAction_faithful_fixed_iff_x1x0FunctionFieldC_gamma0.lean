-- Prove2me | Theorems.Thm_ModularCurve_exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0
-- name    : ModularCurve.exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/c4f12def-e95f-55d0-8044-17322f5c9b2b
-- title:
--   Finite faithful action on the X₁(M)∩ X₀(p) function field with fixed field that of X₀(Mp)
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $L$ be a field of characteristic zero. Inside the Laurent series field $\mathrm{LaurentSeries}\,L$ consider two intermediate fields over $L$. The first, $K_1$, is assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise images, under $\mathbb{Q} \to L$, of the elements of [`ModularCurve.qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)`](def/ModularCurve_X1.html#L101); the latter is the subfield of $\mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by all quotients $pf/pg$ of the Laurent series attached to integral $q$-expansions $pf, pg \in \mathbb{Z}[[q]]$ of two modular forms $f,g$ of one and the same weight $k \in \mathbb{Z}$ for $\Gamma_1(M) \cap \Gamma_0(p)$, with the series of $pg$ nonzero. The second, $K_2$, is assumed equal to the corresponding base change of [`ModularCurve.qExpFunctionFieldC ℚ (Gamma0 (M * p))`](def/ModularCurve_X1.html#L101), and the inclusion $K_2 \le K_1$ is assumed. The conclusion asserts the existence of a type $G$ carrying a group structure, a finite-type structure and an action on $K_1$ by ring automorphisms over the prime field, such that: the action is faithful; every $g \in G$ fixes each $x \in K_1$ whose underlying Laurent series lies in $K_2$; and conversely every $x \in K_1$ fixed by all of $G$ has its underlying Laurent series in $K_2$.
--
--   This is the function-field form, over an arbitrary field of characteristic zero, of the statement that $X(\Gamma_1(M) \cap \Gamma_0(p)) \to X_0(Mp)$ is a Galois covering with deck group the diamond operators $\langle d \rangle$, $d \in (\mathbb{Z}/M)^\times/\{\pm 1\}$: a finite group acts faithfully on the larger $q$-expansion field with fixed field exactly the smaller one, so that by Artin's theorem $K_1/K_2$ is Galois. It is used in the analysis of the integral two-chart model of $X_1(M) \cap X_0(p)$ over $X_0(Mp)$, in particular in the identification of completed local rings at supersingular points and in the invariance of the Gauss valuation subring under the action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥K₁),
      FaithfulSMul G ↥K₁ ∧
      (∀ (g : G) (x : ↥K₁), (x : LaurentSeries L) ∈ K₂ → g • x = x) ∧
      (∀ x : ↥K₁, (∀ g : G, g • x = x) → (x : LaurentSeries L) ∈ K₂) := by sorry
