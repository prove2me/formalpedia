-- Prove2me | Theorems.Thm_ICSCompute_lemma_6_1
-- name    : ICSCompute.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:46:18.113198+00:00
-- url     : https://prove2.me/theorems/92fe294a-667a-46a0-9a35-157358e0292d
-- title:
--   Lemma 6.1 — pairwise characterization of USO outmaps
-- statement:
--   Let $s:\{0,1\}^n\to\{0,1\}^n$. Then:
--
--   1. $s$ is a USO outmap if and only if
--   $$x\neq x' \implies \exists i\in[n]:\ x_i\neq x'_i \ \text{ and }\ s_i(x)\neq s_i(x'). \tag{6.1}$$
--   2. In particular, every USO outmap is a permutation of $\{0,1\}^n$.
--   3. For $h(x) := x\oplus s(x)$, condition (6.1) is equivalent to
--   $$x\neq x' \implies \exists i\in[n]:\ x_i\neq x'_i \ \text{ and }\ h_i(x) = h_i(x'). \tag{6.2}$$
--
--   The pairwise form (6.2) is the hypothesis of the basis-change theorem (Theorem 6.1); this lemma is how the USO promise enters the construction of Theorem 6.2.
--
--   Differences from the source:
--   - generalization: n ∈ ℕ (positive integers; the paper writes ℕ ∪ {0} when 0 is allowed, p.19) → n : ℕ, including n = 0; reason: the n = 0 instance is true (a single vertex, trivial registers); every positive n is an instance
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Lemma 6.1, p.31 (PDF p.33); proof in App. A.1, pp.40–41 (PDF pp.42–43)

import Mathlib
import Definitions.Def_ICSCompute_IsUSOOutmap

namespace ICSCompute

open QAlgorithms

/-- **Lemma 6.1 (Pairwise characterization of USO)** (Shmueli, *What Can Be Computed with
Indefinite Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606,
Lemma 6.1, p.31 (PDF p.33); proof in Appendix A.1, pp.40–41).

A function `s : {0,1}ⁿ → {0,1}ⁿ` is a USO outmap if and only if (6.1) holds:
`x ≠ x′ ⟹ ∃ i : xᵢ ≠ x′ᵢ ∧ sᵢ(x) ≠ sᵢ(x′)`. In particular every USO outmap is a permutation of
`{0,1}ⁿ`. For `h(x) := x ⊕ s(x)`, (6.1) is equivalent to (6.2):
`x ≠ x′ ⟹ ∃ i : xᵢ ≠ x′ᵢ ∧ hᵢ(x) = hᵢ(x′)`.

**Formalization Note** `n : ℕ` includes `n = 0` (one vertex). Bits are `Bool`. -/
theorem lemma_6_1 {n : ℕ} (s : Qubits n → Qubits n) :
    (IsUSOOutmap s ↔ Eq61 s) ∧ (IsUSOOutmap s → Function.Bijective s) ∧
      (Eq61 s ↔ Eq62 (fun x => xorQ x (s x))) := by sorry

end ICSCompute
