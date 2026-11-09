-- Prove2me | Theorems.Thm_OracleStateHSP_theorem_4_10
-- name    : OracleStateHSP.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:09.011202+00:00
-- url     : https://prove2.me/theorems/cb5fedab-9c6b-452c-ad35-c64c9da4bc1d
-- title:
--   Theorem 4.10 (Query lower bound): $\Omega(\log|G/H|/\sqrt\varepsilon)$ queries, even with inverse, conjugate and controlled access
-- statement:
--   There is a universal constant $c > 0$ such that for every $\varepsilon \in (0, 1]$ and all integers $n \ge m > 1$ the following holds for the Fractional Padded Simon's StateHSP family: $r = n - m$, $G = \mathbb Z_2^r \oplus \mathbb Z_2^m \cong \mathbb Z_2^n$ with the shift representation $R$, and for each Simon function $f$ on $\mathbb Z_2^m$ with nonzero period $s(f)$ the preparation unitary $U_\varphi = O^\varepsilon_f W$ and the subgroup $H_f = \mathbb Z_2^r \oplus \langle s(f)\rangle$.
--
--   1. Every member is a StateHSP instance (Definition 1.3) for $R$ with hidden subgroup $H_f$ and parameter $\varepsilon$, and $|G/H_f| = 2^{m-1}$, so $\log|G/H| = m - 1$ is known.
--   2. Let $A$ be any $T$-query algorithm that may use forward queries to $U_\varphi$, inverse queries $U_\varphi^{-1}$, conjugate queries $U_\varphi^*$ and $U_\varphi^T$, in an order fixed in advance, and controlled versions of all of these (through the direct sum $S \oplus (\mathcal H_S \otimes W)$), with a fixed initial state and output map. If $A$ outputs $H_f$ with probability at least $2/3$ for every member of the family, then
--   $$
--   T \;\ge\; c\, \frac{m - 1}{\sqrt{\varepsilon}} = c\,\frac{\log_2 |G/H|}{\sqrt\varepsilon}.
--   $$
--
--   So any quantum algorithm identifying the hidden subgroup with probability at least $2/3$ requires $\Omega(\log|G/H|/\sqrt\varepsilon)$ oracle queries in the worst case. This matches the upper bound of Theorem 3.15 and settles the query complexity of abelian StateHSP.
--
--   **Formalization Note** The algorithm's unitaries, query kinds, initial state and output map are fixed before the instance; the constant $c$ is fixed before $\varepsilon$, $n$ and $m$.
--
--   Differences from the source:
--   - generalization: there is a family of abelian StateHSP instances → the explicit Fractional Padded Simon family of eqs. (53)–(56) used in the paper's proof; reason: an explicit family satisfying the conclusion implies the existential statement
--   - reading: Ω(log|G/H|/√ε) oracle queries → one constant c > 0 chosen before ε, n and m with c(m − 1)/√ε ≤ T; reason: log|G/H| = m − 1 ≥ 1, so footnote 2's max{1, ·} is inactive and the uniform bound is the asymptotic one
--   - reading: known log|G/H| = m − 1 → the clause |G/H_f| = 2^{m−1} for every member, with the algorithm allowed to depend on n and m; reason: the value is the same for every instance of the family
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
--   - encoding: finite-dimensional spaces S and W → S = Fin a, W = Fin b for arbitrary a, b; reason: only the dimensions of S and W matter
--   - encoding: measuring a designated output register → a whole-register computational-basis measurement followed by an output map out; reason: a register measurement is such a map, and out(z) can be written into an output register by one final permutation unitary
--   - encoding: controlled versions of the oracles → the direct sum S ⊕ (H_S ⊗ W) of Definition 4.1; reason: the paper models controlled access this way (p.35)
--   - encoding: access to U_φ, U_φ^{−1}, U_φ^* and U_φ^T → a query kind (fwd, inv, conj, transp) per query, fixed in advance; reason: each query applies one of the four matrices; U^{−1} = U^† for unitary U
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Theorem 4.10, p.40

import Mathlib
import Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb
import Definitions.Def_OracleStateHSP_IsStateHSPInstance
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_hiddenSubgroup
import Definitions.Def_OracleStateHSP_flagZero
import Definitions.Def_OracleStateHSP_shiftRep
import Definitions.Def_OracleStateHSP_fracU

namespace OracleStateHSP

/-- Theorem 4.10 of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.40 (query lower bound): for every `ε ∈ (0, 1]` and integers
`n ≥ m > 1`, there is a family of abelian StateHSP instances with `G = Z_2^n` and known
`log |G/H| = m − 1` such that any quantum algorithm identifying the hidden subgroup with
probability at least `2/3` requires `Ω(log |G/H| / √ε)` oracle queries in the worst case. This
bound holds with access to the state-preparation unitary `U_φ` and its inverse `U_φ^{−1}`, their
complex conjugates `U_φ^*` and `U_φ^T`, and the controlled version of all these oracles.

Here the family is the Fractional Padded Simon's StateHSP family of §4.3 (eqs. (53)–(56)), with
`r = n − m`, `G = Z_2^r ⊕ Z_2^m`, the shift representation `R`, `U_φ = O^ε_f W` and
`H_f = Z_2^r ⊕ ⟨s(f)⟩`, `f` ranging over the Simon functions on `Z_2^m` with nonzero period. There
is one universal `c > 0` such that for all such `ε, n, m`:
1. every member is a StateHSP instance with parameter `ε` (Definition 1.3) and
   `|G/H_f| = 2^{m−1}`;
2. every `T`-query algorithm (any number of forward, inverse, conjugate and transpose queries to
   `U_φ`, in an order fixed in advance, with control through the direct sum of Definition 4.1)
   that outputs `H_f` with probability `≥ 2/3` on every member uses `T ≥ c (m − 1)/√ε` queries.

**Formalization Note.** `Ω` is one constant chosen before `ε`, `n` and `m`; since
`log |G/H| = m − 1 ≥ 1`, footnote 2's `max{1, ·}` is inactive. `Z_2^n` is `Z_2^{n−m} × Z_2^m`. The
algorithm's spaces `S`, `W` are `Fin a`, `Fin b`; the initial state `ψ₀`, the unitaries, the query
kinds and the output map `out` (applied to a whole-register measurement) do not depend on the
instance. -/
theorem theorem_4_10 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ (n m : ℕ), 1 < m → m ≤ n →
      (∀ x : SimonInst m,
          IsStateHSPInstance (shiftRep (n - m) m) (flagZero (n - m) m) (fracU ε (n - m) x.fn)
            (hiddenSubgroup (n - m) x.period) ε ∧
          Nat.card ((K (n - m) × V m) ⧸ hiddenSubgroup (n - m) x.period) = 2 ^ (m - 1)) ∧
      ∀ (T a b : ℕ) (A : QueryAlgorithm (FlagQ (n - m) m) (Fin a) (Fin b) T)
        (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ (FlagQ (n - m) m × Fin b)))
        (out : Fin a ⊕ (FlagQ (n - m) m × Fin b) → AddSubgroup (K (n - m) × V m)),
        ‖ψ₀‖ = 1 →
        (∀ x : SimonInst m, (2 : ℝ) / 3 ≤
          A.outputProb (fracU ε (n - m) x.fn) ψ₀ out (hiddenSubgroup (n - m) x.period)) →
        c * ((m : ℝ) - 1) / Real.sqrt ε ≤ T := by sorry

end OracleStateHSP
