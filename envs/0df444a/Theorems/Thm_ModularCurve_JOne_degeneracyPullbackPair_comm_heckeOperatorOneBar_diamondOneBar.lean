-- Prove2me | Theorems.Thm_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar_diamondOneBar
-- name    : ModularCurve.JOne.degeneracyPullbackPair_comm_heckeOperatorOneBar_diamondOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/29c59220-95f2-5586-885b-b8274c2b41ca
-- title:
--   Degeneracy pull-backs commute with T_q and ⟨ d⟩
-- statement:
--   Fix a nonzero natural number $N$ and a nonzero natural number $\ell$ which is prime and does not divide $N$, and let $N'$ be a natural number with $N' = N\ell$. Assume [`ModularCurve.HeckeDiamondInputsAll`](def/ModularCurve_X1HeckeModule.html#L58) at both levels $N$ and $N'$, i.e. that for every prime the predicate `HeckeInputsOneAlong` holds for the corresponding function field over $\overline{\mathbb Q}$, and that for every $d$ coprime to the level there exist a diamond automorphism of $X_1$'s function field over $\mathbb Q$ satisfying `IsDiamondAut` together with an automorphism of the base-changed field over $\overline{\mathbb Q}$ that is a base change of it. Let $i \in \{0,1\}$ index the pair `degeneracyPullbackPair N N' ℓ` of additive maps $\mathrm{Pic}^0$ of the level-$N$ base-changed $q$-expansion function field $\to$ the corresponding group at level $N'$: when the inputs `DegeneracyPullbackInputs N N' ℓ` hold these are the divisor-class pull-backs along the level inclusion `x1LevelInclBar` and along the substitution `x1LevelSubstBar` (the Hecke-$\beta$ map followed by an $X_1$-into-$X_0$-type level inclusion), and otherwise both are zero. Then for every $x$ in the level-$N$ group: (a) the $i$-th pull-back commutes with `heckeOperatorOneBar` for every prime $q \ne \ell$, and (b) it commutes with `diamondOneBar` at $d$ for every natural number $d$ not divisible by $\ell$.
--
--   This records the standard compatibility of the two degeneracy maps $J_1(N) \to J_1(N\ell)$ with the Hecke operators $T_q$ at primes $q \neq \ell$ and with the diamond operators $\langle d\rangle$ for $\ell \nmid d$, here in the form of divisor-class pull-backs on degree-zero Picard groups of the relevant function fields. It is used in the level-raising/lowering analysis of the Tate modules of $J_1$, in particular in the statements about inertia at $\ell$ and the degeneracy augmentation that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar_diamondOneBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1DegeneracyPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.degeneracyPullbackPair_comm_heckeOperatorOneBar_diamondOneBar
    (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (N' : ℕ) (hN' : N' = N * ℓ)
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hin' : ModularCurve.HeckeDiamondInputsAll N')
    (i : Fin 2) (x : ModularCurve.JOne N) :
    (∀ q : Nat.Primes, (q : ℕ) ≠ ℓ →
        ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i (ModularCurve.heckeOperatorOneBar N q x) =
          ModularCurve.heckeOperatorOneBar N' q (ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i x)) ∧
      ∀ d : ℕ, ¬ ℓ ∣ d →
        ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i (ModularCurve.diamondOneBar N d x) =
          ModularCurve.diamondOneBar N' d (ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i x) := by sorry
