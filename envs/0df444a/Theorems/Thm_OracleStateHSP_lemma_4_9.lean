-- Prove2me | Theorems.Thm_OracleStateHSP_lemma_4_9
-- name    : OracleStateHSP.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:50.973345+00:00
-- url     : https://prove2.me/theorems/8d0e5d70-94de-4878-b516-048e9e553557
-- title:
--   Lemma 4.9 (Padded Simon's lower bound)
-- statement:
--   There is a universal constant $c > 0$ such that the following holds for every $r \ge 0$ and $m \ge 2$, with $K = \mathbb Z_2^r$, $V = \mathbb Z_2^m$ and $G = K \oplus V$ (Definition 4.8).
--
--   1. For every Simon function $f$ on $V$ with nonzero period, the hidden subgroup $\tilde H_f = K \oplus \langle s(f)\rangle$ of $\tilde f(k, v) = f(v)$ has $|\tilde H_f| = 2^{r+1}$; in particular $|\tilde H|$ is the same, known value for every instance.
--   2. Let $A$ be a $T$-query algorithm of Definition 4.1 with oracle $O_{\tilde f}$ of (52), a fixed initial state and an output map into the subgroups of $G$. If $A$ outputs $\tilde H_f$ with probability at least $2/3$ for every such $f$, then
--   $$
--   T \ge c\, m .
--   $$
--
--   So recovering the hidden subgroup of a Padded Simon's problem needs $\Omega(m) = \Omega(\log|G/\tilde H|)$ queries in the worst case, even when $|\tilde H|$ is known.
--
--   Differences from the source:
--   - generalization: queries to O_f (forward) → the model of Definition 4.1: forward and inverse queries, with controlled queries through the direct sum S ⊕ (H_S ⊗ W); reason: p.37 states the bound in this model (O_f is self-inverse and controlled-O_f costs one query); the forward-only bound is the special case
--   - reading: Ω(m) queries → one constant c > 0 chosen before r and m with c·m ≤ T for all r ≥ 0, m ≥ 2; reason: at m = 1, H̃ = G is forced and needs no query; for m ≥ 2 every successful algorithm makes a query, so the uniform bound is equivalent to the asymptotic one
--   - reading: even when |H̃| is known → clause 1 (|H̃_f| = 2^{r+1} for every instance) together with the bound for every algorithm, which may depend on r and m; reason: knowing a value that is the same for all instances is knowing r
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
--   - encoding: measuring a designated output register → a whole-register computational-basis measurement followed by an output map out; reason: a register measurement is such a map, and out(z) can be written into an output register by one final permutation unitary
--   - encoding: finite-dimensional spaces S and W → S = Fin a, W = Fin b for arbitrary a, b; reason: only the dimensions of S and W matter
--   - encoding: f ranges over Simon functions with nonzero period s(f) → x ranges over pairs (f, s) with f hiding s and s ≠ 0; reason: a nonzero period is unique, so the pairs are in bijection with the functions
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Lemma 4.9, p.38; Definition 4.8, p.37

import Mathlib
import Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_paddedOracle
import Definitions.Def_OracleStateHSP_hiddenSubgroup

namespace OracleStateHSP

/-- Lemma 4.9 of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.38 (Padded Simon's lower bound), for the Padded Simon's problems of
Definition 4.8, p.37: any quantum algorithm that recovers the hidden subgroup `H̃ = K ⊕ ⟨s(f)⟩` in
a Padded Simon's problem with success probability at least `2/3` requires `Ω(m)` queries to `O_f̃`
in the worst case, even when `|H̃|` is known.

Here: there is a universal `c > 0` such that for every `r ≥ 0` and `m ≥ 2`,
1. `|H̃_f| = 2^{r+1}` for every instance (the size is known and the same for all `f`);
2. every `T`-query algorithm of Definition 4.1 with oracle `O_f̃` that outputs `H̃_f` with
   probability `≥ 2/3` for every Simon function `f` with nonzero period uses `T ≥ c m` queries.

**Formalization Note.** `Ω(m)` is one constant chosen before `r` and `m`, on `m ≥ 2` (at `m = 1`,
`H̃ = G` is forced and needs no query). Inverse and controlled queries are allowed
(Definition 4.1). `G = Z_2^r × Z_2^m`. -/
theorem lemma_4_9 :
    ∃ c : ℝ, 0 < c ∧ ∀ r m : ℕ, 2 ≤ m →
      (∀ x : SimonInst m, Nat.card (hiddenSubgroup r x.period) = 2 ^ (r + 1)) ∧
      ∀ (T a b : ℕ) (A : QueryAlgorithm ((K r × V m) × V m) (Fin a) (Fin b) T), A.IsDef41 →
      ∀ (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ (((K r × V m) × V m) × Fin b)))
        (out : Fin a ⊕ (((K r × V m) × V m) × Fin b) → AddSubgroup (K r × V m)), ‖ψ₀‖ = 1 →
        (∀ x : SimonInst m, (2 : ℝ) / 3 ≤
          A.outputProb (paddedOracle r x.fn) ψ₀ out (hiddenSubgroup r x.period)) →
        c * m ≤ T := by sorry

end OracleStateHSP
