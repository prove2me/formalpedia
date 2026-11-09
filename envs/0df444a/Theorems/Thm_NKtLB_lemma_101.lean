-- Prove2me | Theorems.Thm_NKtLB_lemma_101
-- name    : NKtLB.lemma_101
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:07:11.700751+00:00
-- url     : https://prove2.me/theorems/74e0202b-4f4e-4fb2-988d-0f693c439daf
-- title:
--   Lemma 101 — String Isolation Lemma
-- statement:
--   There are a deterministic algorithm $A$ and a constant $c$ with the following property. Let $W\subseteq\{0,1\}^n$ be a set of size $l$. Then there is a string $u$ of length $k(n,l)=O(\log(n\cdot l))$ such that $A(1^n,u)$ runs in time $\mathrm{poly}(n)$ and outputs a Boolean circuit computing a function
--   $$
--   H:\{0,1\}^n\to\{0,1\}^{O(\log l)}
--   $$
--   that is injective on $W$: $H(w)\ne H(w')$ for all distinct $w,w'\in W$. Moreover, a uniformly random $u$ of the same length has this property with probability at least $0.99$.
--
--   The lemma lets a short advice string $u$ together with a short hash value $H(x)$ single out $x$ inside a small candidate set. Lemma 100 uses it for this.
--
--   Differences from the source:
--   - encoding: $u\in\{0,1\}^{O(\log(n\cdot l))}$, $\mathrm{poly}(n)$ time, $\{0,1\}^{O(\log l)}$ → one length function $k(n,l)\le c\log(nl)+c$, time $cn^c+c$, at most $c\log l+c$ output bits, with $A$, $c$, $k$ before $n$, $W$; reason: standard meaning of the $O$-bounds; "the same length" in the second sentence is $k(n,l)$
--   - encoding: "outputs a Boolean circuit" → outputs the code `C.encode` of a straight-line circuit; reason: the paper fixes no circuit encoding
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 101, p.68

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_Circuit
import Definitions.Def_NKtLB_prob

namespace NKtLB

/-- **Lemma 101 (String Isolation Lemma [LO21])** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 101, p.68): "There is a
deterministic algorithm `A` for which the following holds. For any set `W ⊆ {0,1}^n` of size `l`,
there exists a string `u ∈ {0,1}^{O(log(n·l))}` such that `A(1^n, u)` runs in `poly(n)` time and
outputs a Boolean circuit that computes a function `H : {0,1}^n → {0,1}^{O(log l)}` with the
following property: `H(w) ≠ H(w′)` for every distinct pair `w, w′ ∈ W`. Moreover, the same guarantee
is achieved by a random string `u` of the same length with probability at least `0.99`."

**Formalization Note.** `A` is a machine of the model; its input is `(1^n, u)` encoded by
`tupleEnc`; "runs in `poly(n)` time" is `c·n^c + c` steps; "outputs a Boolean circuit" is "outputs
`C.encode`"; the seed length is one function `k(n, l) ≤ c·log(n·l) + c` (the "same length" of the
second sentence) and the output length of `H` is at most `c·log l + c`. All constants come before
`n` and `W`. -/
theorem lemma_101 :
    ∃ (A : Machine) (c : ℕ) (k : ℕ → ℕ → ℕ),
      (∀ n l : ℕ, (k n l : ℝ) ≤ c * Real.logb 2 ((n : ℝ) * l) + c) ∧
      ∀ (n : ℕ) (W : Finset (List Bool)), (∀ w ∈ W, w.length = n) →
        (∃ u : List Bool, u.length = k n W.card ∧ ∃ C : Circuit,
          A.Computes (c * n ^ c + c) (tupleEnc [List.replicate n true, u]) C.encode ∧
          (C.outs.length : ℝ) ≤ c * Real.logb 2 W.card + c ∧
          ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → C.eval w ≠ C.eval w') ∧
        (0.99 : ℝ) ≤ prob (k n W.card) (fun u => ∃ C : Circuit,
          A.Computes (c * n ^ c + c) (tupleEnc [List.replicate n true, u]) C.encode ∧
          (C.outs.length : ℝ) ≤ c * Real.logb 2 W.card + c ∧
          ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → C.eval w ≠ C.eval w') := by sorry

end NKtLB
