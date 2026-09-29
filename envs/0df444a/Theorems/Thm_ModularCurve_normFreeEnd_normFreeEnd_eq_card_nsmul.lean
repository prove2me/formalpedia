-- Prove2me | Theorems.Thm_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul
-- name    : ModularCurve.normFreeEnd_normFreeEnd_eq_card_nsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/105b19a0-1d4e-5699-90be-eccdd0f0d529
-- title:
--   The norm-free endomorphism satisfies N∘ N=|Δ| N
-- statement:
--   Let $M$ be a nonzero natural number and $p$ a prime with $p \mid M$, and assume the predicate [`ModularCurve.HeckeDiamondInputsAll M`](def/ModularCurve_X1HeckeModule.html#L58), i.e. that for every prime $\ell$ the Hecke inputs `HeckeInputsOneAlong` hold for $M$ and $\ell$ over $\overline{\mathbb{Q}}$, and that for every $d$ coprime to $M$ there is an automorphism of the function field `x1FunctionField M` over $\mathbb{Q}$ satisfying `IsDiamondAut M d` and an automorphism of `x1FunctionFieldBar M` over $\overline{\mathbb{Q}}$ which is a base change of `diamondAut M d` in the sense of `IsBaseChangeAutOf`. Let $S =$ `normFreeRepsAt M p` be the finite set of $d < M$ with $d$ coprime to $M$ and $d \equiv 1 \pmod{M/p}$, and let $N =$ `normFreeEnd M S` be the additive endomorphism $x \mapsto |S| \cdot x - \sum_{d \in S} \langle d\rangle x$ of $J_1(M) =$ `JOne M`, the group of degree-zero divisor classes of `x1FunctionFieldBar M` over $\overline{\mathbb{Q}}$ modulo principal divisors, where $\langle d\rangle =$ `diamondOneBar M d` is the diamond operator attached to $d$. Then for every $x \in J_1(M)$ one has $N(N x) = |S| \cdot N x$.
--
--   The endomorphism $N$ is the norm-free (Mazur–Wiles) operator attached to the kernel $\Delta$ of $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, and the identity says that $N$ is $|\Delta|$ times an idempotent, so that $N$ cuts out the norm-free part of $J_1(M)$ after inverting $|\Delta|$. It feeds the construction of the norm-free part of the model of $X_1$ at $p$ and the vanishing statements for the associated Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_normFreeEnd_normFreeEnd_eq_card_nsmul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.normFreeEnd_normFreeEnd_eq_card_nsmul
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M)
    (hIn : ModularCurve.HeckeDiamondInputsAll M) (x : JOne M) :
    normFreeEnd M (normFreeRepsAt M p) (normFreeEnd M (normFreeRepsAt M p) x) =
      (normFreeRepsAt M p).card • normFreeEnd M (normFreeRepsAt M p) x := by sorry
