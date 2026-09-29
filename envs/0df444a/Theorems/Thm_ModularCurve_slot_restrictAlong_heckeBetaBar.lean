-- Prove2me | Theorems.Thm_ModularCurve_slot_restrictAlong_heckeBetaBar
-- name    : ModularCurve.slot_restrictAlong_heckeBetaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/71c19e79-6820-5252-bcca-c77b07bbe8d6
-- title:
--   Slot data under restriction along `heckeBetaBar`
-- statement:
--   Let $K$ be a field of characteristic $0$ equipped with a $\mathbb{Q}$-algebra structure, let $N\ge 1$ and let $\ell$ be a prime with $\ell\nmid N$, and assume `HeckeBetaBarIntegral K N ℓ`, i.e. that the ring homomorphism underlying the $K$-algebra map $\bar\beta=$ `heckeBetaBar K N ℓ` from $\mathrm{laurentBaseChange}\,K\,(\mathrm{modularFunctionFieldFull}\,N)$ to $\mathrm{laurentBaseChange}\,K\,(\mathrm{modularFunctionFieldFull}\,(N\ell))$, which acts by $q\mapsto q^{\ell}$ on $q$-expansions, is integral. Let $\zeta\in K^{\times}$ be a primitive $N\ell$-th root of unity, let $a\mid N\ell$ with $a\neq 0$ and $b\in\mathbb{N}$. Let $\iota$ be a $K$-algebra homomorphism from the level-$N\ell$ base-changed field to $K((q))$ sending the image of $j$ to $\mathrm{qExpand}\,K\,(N\ell)$ of that image, and the image of $j(q^{N\ell})$ to $\mathrm{qExpand}\,K\,(a\cdot a)$ of the $q$-twist of $j$ by $\zeta^{ba}$. Let $W$ be a place of the level-$N\ell$ base-changed field and $\gamma>0$ an integer with $\operatorname{ord}_W(x)\cdot\gamma=\operatorname{order}(\iota x)$ for all $x$. The conclusion is twofold: the ramification index of $W$ along $\bar\beta$, namely the least $n>0$ of the form $\operatorname{ord}_W(\bar\beta f)$ with $f\neq 0$, equals $\gcd(a,\ell)$; and there are $a_0\neq0$, $b_0$ and a $K$-algebra homomorphism $\iota_0$ from the level-$N$ base-changed field to $K((q))$ with $a_0\gcd(a,\ell)=a$, with $\iota_0$ of the same shape at level $N$ with data $(a_0,b_0)$ relative to $\zeta^{\ell}$, with $\operatorname{ord}_{W'}(x)\cdot\bigl(a_0\gcd(a_0,N/a_0)\bigr)=\operatorname{order}(\iota_0 x)$ for all $x$, where $W'$ is the restriction of $W$ along $\bar\beta$, and with $(\ell/\gcd(a,\ell))\,b_0\equiv b \pmod{\gcd(a_0,N/a_0)}$.
--
--   This is the cusp-theoretic statement that a cusp of $X_0(N\ell)$ carrying slot data $(a,b)$ lies, under the degeneracy map induced by $q\mapsto q^{\ell}$, over the cusp of $X_0(N)$ with width parameter $a/\gcd(a,\ell)$, with ramification index $\gcd(a,\ell)$ and with the twist label transported by multiplication by $\ell/\gcd(a,\ell)$. It feeds the construction of pairs of places in a fibre of $\bar\beta$ used in [`ModularCurve.exists_pair_fiberAlong_heckeBetaBar_of_ord_neg`](thm.html#ModularCurve.exists_pair_fiberAlong_heckeBetaBar_of_ord_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_slot_restrictAlong_heckeBetaBar.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.slot_restrictAlong_heckeBetaBar (K : Type*) [Field K] [Algebra ℚ K] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hβ : HeckeBetaBarIntegral K N ℓ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (N * ℓ)) (a b : ℕ) (ha : a ∣ N * ℓ) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull (N * ℓ)) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full (N * ℓ))⟩ =
        qExpand K (N * ℓ) (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN (N * ℓ)), coeffEmb_mem_laurentBaseChange K (jqd_mem_full (N * ℓ) (dvd_refl (N * ℓ)))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (W : Place K (laurentBaseChange K (modularFunctionFieldFull (N * ℓ)))) (γ : ℤ) (hγ : 0 < γ)
    (hW : ∀ x, W.ord x * γ = (ι x).order) :
    W.ramificationIndexAlong (heckeBetaBar K N ℓ) = Nat.gcd a ℓ ∧
    ∃ (a₀ b₀ : ℕ) (_ : NeZero a₀)
      (ι₀ : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K),
      a₀ * Nat.gcd a ℓ = a ∧
      ι₀ ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι₀ ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a₀ * a₀) (qTwist ((ζ ^ ℓ) ^ (b₀ * a₀)) (coeffEmb K jq)) ∧
      (∀ x, (W.restrictAlong (heckeBetaBar K N ℓ) hβ).ord x * ((a₀ * Nat.gcd a₀ (N / a₀) : ℕ) : ℤ)
          = (ι₀ x).order) ∧
      ℓ / Nat.gcd a ℓ * b₀ ≡ b [MOD Nat.gcd a₀ (N / a₀)] := by sorry
