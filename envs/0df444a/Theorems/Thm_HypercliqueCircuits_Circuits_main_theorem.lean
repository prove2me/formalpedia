-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_main_theorem
-- name    : HypercliqueCircuits.Circuits.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:36:18.627801+00:00
-- url     : https://prove2.me/theorems/4b6dc422-ebb1-4c5c-93c2-e57fa271e8c1
-- title:
--   Theorem 1 — uniform sub-brute-force dyadic hyperclique circuits
-- statement:
--   For every fixed $k\ge3$, the formal hyperclique polynomial $\Delta_n^{(k)}$ has uniformly constructible circuits with literal constants in $D=\mathbb Z[1/2]$. Use the sequence displayed in the proof:
--
--   $$\epsilon_3=1/8,\quad L_j=\log_2(1/\epsilon_j),\quad B_j=\lceil8L_j/\epsilon_j\rceil,\quad\epsilon_{j+1}=\epsilon_j/(4B_j).$$
--
--   Every $\epsilon_k$ is positive. There are absolute $a,b>0$ and a threshold $K$ such that $a2^k\le\log_2(1/\epsilon_k)\le b2^k$ for all $k\ge\max(K,3)$, expressing $\epsilon_k=2^{-\Theta(2^k)}$.
--
--   One finite deterministic program, independent of $k,n$ and runtime slack, takes unary $(1^n,1^k)$ and outputs a complete circuit $C_{k,n}$ for every $n\ge1$, with
--
--   $$\llbracket C_{k,n}\rrbracket=\Delta_n^{(k)},\qquad |C_{k,n}|\le C_k n^{k-\epsilon_k}.$$
--
--   For each $k\ge3$ and each $\eta>0$, the same program eventually uses at most $C_{k,\eta}n^{k-\epsilon_k+\eta}$ bit cost, including memory access and serialization of gate records, pointers and actual dyadic numerators and exponents. The same $\epsilon_k$ and size constant occur in both clauses. This is the full symbolic and uniform target, without any evaluation or hypergraph-input restriction.
--
--   Differences from the source:
--   - reading: arithmetic circuit size without a leaf-count convention → total vertices, including all declared variable sources and literal constant sources; output pointers are free; reason: fixes one size convention for every result; sharing and exact factors are audited in MODERATION_NOTES.md
--   - encoding: one-based coordinate tuples and deletion of position j → Fin coordinates and functions on the ordered subtype of positions other than j; reason: the increasing-coordinate bijection preserves all variables and every monomial
--   - encoding: epsilon_k=2^(-Theta(2^k)) with the proof giving a recurrence → the exact proof recurrence and eventual two-sided bounds on binary log(1/epsilon_k); reason: specifies a source witness and quantifies both absolute constants before k
--   - encoding: O circuit size and fixed-k o(1) runtime → one size constant per k for all positive n, and a time constant and threshold for each k and positive slack eta; reason: the same program and saving are used for every slack; finite initial sizes are absorbed
--   - reading: uniform circuit construction and its time bound → a finite deterministic binary-integer RAM with explicit unary input, serialized literal output, and quadratic accessed-word-length cost; reason: charges real execution and every output bit; polylogarithmic bookkeeping fits the source o(1) term
--   - encoding: formal polynomials with constants in Z[1/2] → literal pairs (a,b) in Int times Nat, interpreted as a/2^b in rational multivariate polynomials; reason: these pairs represent exactly the dyadic subring, whose inclusion into the rationals is injective, so formal polynomial equality has the same instances
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Theorem 1, p.2 (PDF 3), proof and saving recurrence p.24 (PDF 25).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Theorem 1, printed p.2 / PDF 3; source recurrence on printed p.24 / PDF 25.
One finite bit-cost RAM program, with every output bit and coefficient charged.
No algorithm, runtime or correctness certificate is supplied as an input hypothesis. -/
theorem main_theorem :
    (∀ k : ℕ, 3 ≤ k → 0 < saving k) ∧
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 3 ≤ k →
      a * (2 : ℝ)^k ≤ Real.logb 2 (1/saving k) ∧
      Real.logb 2 (1/saving k) ≤ b * (2 : ℝ)^k) ∧
    ∃ prog : Program Empty, ∀ k : ℕ, 3 ≤ k →
      ∃ Csize : ℝ, 0 < Csize ∧
        (∀ n : ℕ, 0 < n → ∃ t : ℕ, ∃ c : Circuit Dyadic (UniformVar k n) 1,
          Generates prog k n t c ∧ (c.size : ℝ) ≤ Csize*(n : ℝ)^((k : ℝ)-saving k)) ∧
        (∀ η : ℝ, 0 < η → ∃ Ctime : ℝ, 0 < Ctime ∧ ∃ N : ℕ,
          ∀ n : ℕ, N ≤ n → 0 < n → ∃ t : ℕ, ∃ c : Circuit Dyadic (UniformVar k n) 1,
            Generates prog k n t c ∧ (c.size : ℝ) ≤ Csize*(n : ℝ)^((k : ℝ)-saving k) ∧
            (executionBits Empty.elim prog (unaryInput k n) t : ℝ) ≤
              Ctime*(n : ℝ)^((k : ℝ)-saving k+η)) := by sorry

end HypercliqueCircuits.Circuits
