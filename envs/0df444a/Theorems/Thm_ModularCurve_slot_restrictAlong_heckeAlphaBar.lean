-- Prove2me | Theorems.Thm_ModularCurve_slot_restrictAlong_heckeAlphaBar
-- name    : ModularCurve.slot_restrictAlong_heckeAlphaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/69de58a4-05fe-5545-b4a8-4ceb1e1a66d6
-- title:
--   Restriction of a slot place along ᾱ from level Nℓ
-- statement:
--   Let $K$ be a field with a $\mathbb{Q}$-algebra structure, $N$ a nonzero natural number and $\ell$ a prime with $\ell \nmid N$, and assume `HeckeAlphaBarIntegral K N ℓ`, i.e. the ring homomorphism underlying `heckeAlphaBar K N ℓ` — the inclusion of $F_N :=$ `laurentBaseChange K (modularFunctionFieldFull N)`, the subfield of $K((q))$ generated over $K$ by the coefficientwise image of the full level-$N$ modular function field, into $F_{N\ell}$ — is integral. Let $\zeta \in K^\times$ be a primitive $(N\ell)$-th root of unity, and $a \mid N\ell$ nonzero, $b$ a natural number. Let $\iota : F_{N\ell} \to K((q))$ be a $K$-algebra homomorphism sending the class of $j$ to $\mathrm{qExpand}\,(N\ell)$ of $j$ and the class of $j(q^{N\ell})$ to $\mathrm{qExpand}\,(a^2)$ of $\mathrm{qTwist}\,(\zeta^{ba})$ of $j$, and let $W$ be a place of $F_{N\ell}$ (a proper principal valuation subring containing $K$) such that $\mathrm{ord}_W(x)\cdot\gamma = \mathrm{order}(\iota x)$ for all $x$, for some integer $\gamma > 0$. Then the ramification index of $W$ along `heckeAlphaBar K N ℓ` (the least positive value of $\mathrm{ord}_W$ on nonzero elements of $F_N$) times $\gcd(a,\ell)$ equals $\ell$; and there are nonzero $a_0$, a natural number $b_0$, and a $K$-algebra homomorphism $\iota_0 : F_N \to K((q))$ with $a_0\gcd(a,\ell) = a$, with $\iota_0$ sending the class of $j$ to $\mathrm{qExpand}\,N$ of $j$ and the class of $j(q^N)$ to $\mathrm{qExpand}\,(a_0^2)$ of $\mathrm{qTwist}\,((\zeta^{\ell})^{b_0a_0})$ of $j$, such that $\mathrm{ord}_{W'}(x)\cdot a_0\gcd(a_0,N/a_0) = \mathrm{order}(\iota_0 x)$ for all $x$, where $W'$ is the restriction of $W$ to $F_N$ along `heckeAlphaBar K N ℓ`, and $\gcd(a,\ell)\,b_0 \equiv b \pmod{\gcd(a_0,N/a_0)}$.
--
--   This is the cuspidal ramification computation for the degeneracy map $X_0(N\ell) \to X_0(N)$ in the present function-field setting: a place presented in slot normal form with data $(a,b)$ relative to $\zeta$ at level $N\ell$ restricts to a place in slot normal form with data $(a_0,b_0)$ relative to $\zeta^{\ell}$ at level $N$, where $a_0 = a/\gcd(a,\ell)$, the twist label descends modulo $\gcd(a_0,N/a_0)$, and the ramification index is $\ell/\gcd(a,\ell)$. It is used in the analysis of fibres of the second degeneracy map, in [`ModularCurve.exists_pair_fiberAlong_heckeBetaBar_of_ord_neg`](thm.html#ModularCurve.exists_pair_fiberAlong_heckeBetaBar_of_ord_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_slot_restrictAlong_heckeAlphaBar.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.slot_restrictAlong_heckeAlphaBar (K : Type*) [Field K] [Algebra ℚ K] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hα : HeckeAlphaBarIntegral K N ℓ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (N * ℓ)) (a b : ℕ) (ha : a ∣ N * ℓ) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull (N * ℓ)) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full (N * ℓ))⟩ =
        qExpand K (N * ℓ) (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN (N * ℓ)), coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_refl (N * ℓ)))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (W : Place K (laurentBaseChange K (modularFunctionFieldFull (N * ℓ)))) (γ : ℤ) (hγ : 0 < γ)
    (hW : ∀ x, W.ord x * γ = (ι x).order) :
    W.ramificationIndexAlong (heckeAlphaBar K N ℓ) * Nat.gcd a ℓ = ℓ ∧
    ∃ (a₀ b₀ : ℕ) (_ : NeZero a₀)
      (ι₀ : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K),
      a₀ * Nat.gcd a ℓ = a ∧
      ι₀ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι₀ ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a₀ * a₀) (qTwist ((ζ ^ ℓ) ^ (b₀ * a₀)) (coeffEmb K jq)) ∧
      (∀ x, (W.restrictAlong (heckeAlphaBar K N ℓ) hα).ord x * ((a₀ * Nat.gcd a₀ (N / a₀) : ℕ) : ℤ)
          = (ι₀ x).order) ∧
      Nat.gcd a ℓ * b₀ ≡ b [MOD Nat.gcd a₀ (N / a₀)] := by sorry
