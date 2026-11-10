-- Prove2me | Theorems.Thm_ObfEF_Incremental_lemma_3_4
-- name    : ObfEF.Incremental.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:57:17.12089+00:00
-- url     : https://prove2.me/theorems/524a94ef-b98a-4606-a091-68079ccab893
-- title:
--   Lemma 3.4 — changing the cells of J is an incremental change with |S| ≤ 8|J|(il+M+ol) and circuits of size ≤ |J|+2
-- statement:
--   Let $il,ol,M\ge1$ and let $D$ and $D'$ be proper configurations of $U_{il,ol,M}$ (Definition 3.3) with the same selections of the outputs that differ only at constants of the cells of a set $J$. Let $R$ be the set of the wires outside the outputs of the cells of $J$ that cells of $J$ select in $D$ or in $D'$, and let $\hat w$ and $\hat w'$ be the functions computed by the cells of $J$ in $D$ and in $D'$ when the values at $R$ are treated as independent inputs. Suppose that $\hat w_j=\hat w'_j$ for every $j\in J$ whose output some cell outside $J$ or some output selects. Then there is an incremental change $(S,R,\Gamma)$ from $D$ to $D'$ with
--   $$|S|\le 8\,|J|\,(il+M+ol)\qquad\text{and}\qquad |\Gamma_o|,|\Gamma'_o|\le |J|+2\ \text{ for every output wire } o \text{ of a gate of } S.$$
--
--   This is the basic move of the rewriting: changing a few instructions of the universal topology, while the instructions read from outside keep their functions, is a change whose support is the set of operand wires and whose internal values have constant-size descriptions.
--
--   Differences from the source:
--   - encoding: proper configurations D, D′ with the same output selections that differ only at constants of the cells of J → valid instruction data p, p′ (Prog.Valid) with p.sel = p′.sel on the outputs and p.instr = p′.instr outside J; D = p.toConfig, D′ = p′.toConfig; reason: on the constants of U a proper configuration is exactly the configuration of its cell instructions and output selections
--   - encoding: cells j ∈ [M], wires w_1, …, w_{il+M} → 0-based cells j < M and w-indices i < il + M (w_i for i < il an input, w_{il+j} the output of cell j); R as the set of wires Uw i of these indices; reason: Lean convention; same objects
--   - encoding: ŵ_j : {0,1}^R → {0,1} → hatW il M p J j ρ for ρ : ℕ → Bool giving all values outside the outputs of J; reason: the cells of J read only wires of R or outputs of J, so hatW depends on ρ only through R
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 47, Lemma 3.4

import Mathlib
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_GateList
import Definitions.Def_ObfEF_Incremental_IncrementalChange
import Definitions.Def_ObfEF_Incremental_Cells

namespace ObfEF.Incremental

/-- Lemma 3.4 (Incremental Changes of Cells). Proper configurations `D = p.toConfig` and
`D' = p'.toConfig` of `U_{il,ol,M}` with the same output selections that differ only in the cells
of `J`; `R` is the set of wires outside the outputs of the cells of `J` that cells of `J` select in
`D` or `D'`. If `ŵ_j = ŵ'_j` for every `j ∈ J` whose output a cell outside `J` or an output
selects, there is an incremental change `(S, R, Γ)` from `D` to `D'` with
`|S| ≤ 8|J|(il + M + ol)` and every describing circuit of size at most `|J| + 2`. -/
theorem lemma_3_4 (il ol M : ℕ) (hil : 1 ≤ il) (hol : 1 ≤ ol) (hM : 1 ≤ M)
    (p p' : Prog) (hp : p.Valid il ol M) (hp' : p'.Valid il ol M)
    (J : Finset ℕ) (hJ : ∀ j ∈ J, j < M)
    (hsel : ∀ k < ol, p.sel k = p'.sel k)
    (hdiff : ∀ j < M, j ∉ J → p.instr j = p'.instr j)
    (hfun : ∀ j ∈ J,
      ((∃ j' < M, j' ∉ J ∧ il + j ∈ (p.instr j').selects) ∨ (∃ k < ol, p.sel k = il + j)) →
        ∀ ρ : ℕ → Bool, hatW il M p J j ρ = hatW il M p' J j ρ) :
    ∃ ch : IncrementalChange (U il ol M) (labels il ol M p.toConfig) (labels il ol M p'.toConfig),
      ch.R = ((J.biUnion fun j => (p.instr j).selects ∪ (p'.instr j).selects).filter
                (fun i => ∀ j ∈ J, i ≠ il + j)).image (Uw il ol M) ∧
      ch.S.card ≤ 8 * J.card * (il + M + ol) ∧
      ∀ j ∈ ch.S, (ch.Γ j).size ≤ J.card + 2 ∧ (ch.Γ' j).size ≤ J.card + 2 := by sorry

end ObfEF.Incremental
