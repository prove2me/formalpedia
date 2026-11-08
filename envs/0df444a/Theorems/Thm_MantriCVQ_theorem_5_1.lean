-- Prove2me | Theorems.Thm_MantriCVQ_theorem_5_1
-- name    : MantriCVQ.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:07.438037+00:00
-- url     : https://prove2.me/theorems/27f221c1-cb81-41c8-ab5e-8a9781c22d53
-- title:
--   Theorem 5.1 — exact quantum evaluation
-- statement:
--   Fix an admissible gate set and a code family of degree $d$ over it. There is a uniform clean quantum algorithm that, on every valid tree of height $j$, computes the value of the tree exactly with $3^j$ queries to the leaves and in time $3^j\,\mathrm{poly}(n,j)$. Clean means that it adds the value to an output qubit and returns all work registers to their initial states, and the address of the node sits in a register it never modifies:
--   $$|w_0\rangle|b\rangle|0\cdots0\rangle\mapsto|w_0\rangle|b\oplus\mathrm{val}(w_0)\rangle|0\cdots0\rangle.$$
--   This gives $L\in\mathsf{EQP}^O$.
--
--   Differences from the source:
--   - reading: uniform clean algorithm, 3^j queries, time 3^j poly(n, j) → the exact action on basis states, exactly 3^j oracle gates, circuit size and ancillas at most 3^j p(n + j); reason: the formal content of the paper's words; a bivariate polynomial and a polynomial in n + j bound each other
--   - reading: the same uniformly generated circuit at each height → the generator reads 1^n, 1^h and 1^j; reason: the address register's length depends on the height h of the instance; h is at most log n, so this adds nothing
--   - reading: queries to the leaves → any oracle O whose table at 1^n 0 w is the tree's leaf table; reason: the layout of §7.1
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 5.1, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_MantriCVQ_Addr
import Definitions.Def_MantriCVQ_Admissible
import Definitions.Def_MantriCVQ_CodeFamily
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_leafTable
import Definitions.Def_MantriCVQ_nodeVal

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- **Theorem 5.1** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 5.1, p. 19 (PDF p. 21)): there is a uniform clean quantum algorithm that, on every
valid tree of height `j`, computes the value of the tree exactly with `3^j` queries to the leaves and in time
`3^j poly(n, j)`.

**Formalization Note** The registers are address, output and work. On `|w₀⟩|b⟩|0…0⟩`, with `w₀` the address of a node
of height `j` whose subtree is valid, the circuit gives `|w₀⟩|b ⊕ val(w₀)⟩|0…0⟩` (clean, §5.1, p. 18). "`3^j` queries"
is exactly `3^j` oracle gates, and "time" is circuit size and ancilla count, with `poly(n, j)` written as a polynomial
in `n + j`. The address register has a length that depends on the height `h` of the instance, so the generator also
reads `1^h`; `h ≤ log n`, so this adds nothing. The oracle is any `O` with `O(1^n 0 w)` the leaf `w`. -/
theorem theorem_5_1 {G : List Gate} (hG : Admissible G) {d : ℕ} (C : CodeFamily G d) :
    ∃ (anc : ℕ → ℕ → ℕ → ℕ)
      (A : (n h j : ℕ) → Circ G (addrLen (dimsRange n j (h - j)) + (1 + anc n h j)))
      (p : Polynomial ℕ),
      (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n h j : ℕ, 1 ≤ n → j ≤ h → h ≤ hmax n →
        f (tup [unary n, unary h, unary j]) = encNat (anc n h j) ++ (A n h j).enc) ∧
      ∀ n h j : ℕ, 1 ≤ n → j ≤ h → h ≤ hmax n →
        (A n h j).size ≤ 3 ^ j * p.eval (n + j) ∧ anc n h j ≤ 3 ^ j * p.eval (n + j) ∧
        (A n h j).queries = 3 ^ j ∧
        ∀ (O : Oracle) (w₀ : Addr (dimsRange n j (h - j))) (b : Bool),
          Valid C.code (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w₀) →
          (A n h j).run O (ket _ (Addr.toStr _ w₀ ++ b :: List.replicate (anc n h j) false)) =
            ket _ (Addr.toStr _ w₀ ++
              xor b (nodeVal C.code (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w₀)) ::
                List.replicate (anc n h j) false) := by sorry

end MantriCVQ
