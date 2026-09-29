-- Prove2me | Theorems.Thm_ModularCurve_exists_slot_of_ord_jqModC_neg
-- name    : ModularCurve.exists_slot_of_ord_jqModC_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/ac595276-16f1-5aed-b43b-73cdeafd0548
-- title:
--   Poles of jmath̄ on the full level-N field are slot places
-- statement:
--   Let $K$ be an algebraically closed field, let $N\ge 1$ be a natural number with $N\ne 0$ in $K$, and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $N$-th root of unity. Write $F=$ `modularFunctionFieldFullC K N` for the intermediate field of $K((q))=$ `LaurentSeries K` obtained by adjoining to $K$ all series $\mathrm{qExpand}_d(\bar\jmath)$ (substitution $q\mapsto q^{d}$ applied to $\bar\jmath$) for the nonzero divisors $d$ of $N$, where $\bar\jmath=$ `jqModC K` is $q^{-1}$ times the image in $K$ of the integral power series $E_4^3\cdot\eta^{-24}$-type numerator `jNum`. Let $w$ be a place of $F$ over $K$, i.e. a proper valuation subring of $F$ containing $K$ whose ring is a principal ideal ring, and suppose $\mathrm{ord}_w(\bar\jmath)<0$, the order being $-\log$ of the associated adic valuation. Then there are natural numbers $a,b$ with $a\mid N$, $a\neq 0$, $b<N/a$ and $\gcd(\gcd(a,b),N/a)=1$, together with a $K$-algebra homomorphism $\iota\colon F\to K((q))$ such that $\iota(\bar\jmath)=\bar\jmath(q^{N})$, $\iota\bigl(\bar\jmath(q^{N})\bigr)=\bar\jmath(\zeta^{ba}q^{a^{2}})$ (the twist $q\mapsto uq$ being `qTwist` and the substitution $q\mapsto q^{a^2}$ being `qExpand`), and $\mathrm{ord}_w(x)\cdot a\gcd(a,N/a)=\mathrm{ord}_q(\iota(x))$ for every $x\in F$, where $\mathrm{ord}_q$ is the order of a Laurent series.
--
--   This is the classical description of the cusps of $X_0(N)$: every place of the level-$N$ modular function field at which $\bar\jmath$ has a pole is the pull-back of the $q$-adic valuation along one of the slot embeddings attached to a matrix $\begin{pmatrix} a & b\\ 0 & N/a\end{pmatrix}$, with explicit ramification factor $a\gcd(a,N/a)$, here in the form valid whenever $N$ is invertible in $K$. It is used to compute the order of $\bar\jmath(q^N)$ at such a place, in [`ModularCurve.cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg`](thm.html#ModularCurve.cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_slot_of_ord_jqModC_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_slot_of_ord_jqModC_neg
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldFullC K N))
    (hw : w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0) :
    ∃ a b : ℕ, a ∣ N ∧ b < N / a ∧ Nat.gcd (Nat.gcd a b) (N / a) = 1 ∧
      ∃ (_ : NeZero a) (ι : ↥(modularFunctionFieldFullC K N) →ₐ[K] LaurentSeries K),
        ι ⟨jqModC K, jqModC_mem_full K N⟩ = qExpand K N (jqModC K) ∧
        ι ⟨qExpand K N (jqModC K), jqModCd_mem_full K N (dvd_refl N)⟩ =
            qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)) ∧
        ∀ x, w.ord x * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) = (ι x).order := by sorry
