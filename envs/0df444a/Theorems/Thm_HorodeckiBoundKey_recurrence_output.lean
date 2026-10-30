-- Prove2me | Theorems.Thm_HorodeckiBoundKey_recurrence_output
-- name    : HorodeckiBoundKey.recurrence_output
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:50.653098+00:00
-- url     : https://prove2.me/theorems/1addb47c-4acf-4f5b-b45b-38e98ab8fd81
-- title:
--   Eq. (12): the recurrence step on $n$ copies of (11) outputs $N\rho'$
-- statement:
--   Let $d\ge 2$, $l\ge 1$, $n\ge 1$ and $0\le p\le\frac12$, and let $\rho$ be the state (11) built from the hiding states $\tau_0,\tau_1$ of (10). Take $n$ copies and let each party apply $J^\dagger\otimes\mathbb 1$ to its $n$ key qubits and $n$ shields, where $J|i\rangle = |i\cdots i\rangle$ (the successful branch of the recurrence protocol of [23] without twirling). Then
--   $$
--   (J_A^\dagger\otimes J_B^\dagger\otimes\mathbb 1)\,\rho^{\otimes n}\,(J_A\otimes J_B\otimes\mathbb 1) = N\,\rho',\qquad N = 2p^n + 2\left(\tfrac12-p\right)^n > 0,
--   $$
--   where $\rho'$ is the block matrix (12), and $\rho'$ is a state.
--
--   So the branch succeeds with probability $N$ and leaves the state $\rho'$, whose off-diagonal block is the $n$-th tensor power of that of $\rho$.
--
--   **Formalization Note** $\rho^{\otimes n}$ is `keyPower`, $J^\dagger\otimes\mathbb 1$ is `repetitionDecoder`, and the product of the two parties' operators is `localPair`. The shields of $\rho'$ are Alice's $n$ copies of $A'$ and Bob's $n$ copies of $B'$.
--
--   Differences from the source:
--   - reading: "apply the recurrence distillation protocol of [23] without the twirling step. The resulting state is ρ′" → the branch operator J† ⊗ J† ⊗ 1 (all target outcomes 0) maps ρ^{⊗n} to N·ρ′; reason: the normalization N printed after (12) is exactly the probability of this branch; the other agreeing-outcome branches give the same normalized state, and the paper does not single one out
--   - encoding: ρ^{⊗n} and the shields of ρ′ as (A′B′)^{⊗n} → copies regrouped as key pairs × Alice's n shields × Bob's n shields; reason: a fixed permutation of tensor factors that keeps each register with its owner
--   - encoding: the parameters of (11)–(12), left implicit → d ≥ 2, l ≥ 1, n ≥ 1, 0 ≤ p ≤ 1/2; reason: ϱ_a of (9) needs d ≥ 2, (11) is a state only for 0 ≤ p ≤ 1/2, and "n copies" means n ≥ 1; the conditions exclude only undefined cases
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, eq. (12), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_keyPower
import Definitions.Def_HorodeckiBoundKey_localPair
import Definitions.Def_HorodeckiBoundKey_repetitionDecoder
import Definitions.Def_HorodeckiBoundKey_recurrenceNorm
import Definitions.Def_HorodeckiBoundKey_recurrenceOutput

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (hidingFamily)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, eq. (12), p.3: "Now,
we take n copies, and apply the recurrence distillation protocol of [23] without the twirling
step. The resulting state is ρ′ = 1/N [block matrix] (12) where N = 2pⁿ + 2(1/2 − p)ⁿ."

Let `d ≥ 2`, `l ≥ 1`, `n ≥ 1` and `0 ≤ p ≤ 1/2`, and let `ρ` be the state (11)
(`hidingFamily p d l`). Let each party apply `J† ⊗ 𝟙` (`repetitionDecoder`) to its `n` key
qubits and `n` shields of `ρ^{⊗n}`. Then
`(J†_A ⊗ J†_B ⊗ 𝟙) ρ^{⊗n} (J_A ⊗ J_B ⊗ 𝟙) = N · ρ′`, with `N = 2pⁿ + 2(½ − p)ⁿ > 0` and `ρ′` the
block matrix (12) (`recurrenceOutput p d l n`); and `ρ′` is a state.

**Formalization Note.** `J†` is the Kraus operator of the branch of the recurrence step in which
all measured target pairs give outcome 0; `N` is its probability. The `n`-copy state is
`keyPower` (copies regrouped as key pairs × Alice's shields × Bob's shields), and the shields of
`ρ′` are Alice's `n` copies × Bob's `n` copies (`bipartiteCopies`). -/
theorem recurrence_output (p : ℝ) (d l n : ℕ) (hd : 2 ≤ d) (hl : 1 ≤ l) (hn : 1 ≤ n)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    localPair (repetitionDecoder n (Fin l → Fin d)) (repetitionDecoder n (Fin l → Fin d)) *
        keyPower (hidingFamily p d l) n *
        (localPair (repetitionDecoder n (Fin l → Fin d))
          (repetitionDecoder n (Fin l → Fin d)))ᴴ =
      ((recurrenceNorm p n : ℝ) : ℂ) • recurrenceOutput p d l n ∧
    0 < recurrenceNorm p n ∧ IsDensityMatrix (recurrenceOutput p d l n) := by sorry

end HorodeckiBoundKey
