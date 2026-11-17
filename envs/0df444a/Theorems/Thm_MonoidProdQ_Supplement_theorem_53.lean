-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_53
-- name    : MonoidProdQ.Supplement.theorem_53
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:23:57.112416+00:00
-- url     : https://prove2.me/theorems/1d14d342-c7dd-449c-b4f2-9a493acf80d6
-- title:
--   Theorem 53 — Schützenberger decomposition of $P_m$
-- statement:
--   Let $M$ be a finite aperiodic monoid and $m\in M$ with rank $\rho(m)=|M|-|MmM|>0$. Define
--   $$\begin{aligned}E&=\{(r,a):raM=mM,\ rM\ne mM\},\qquad F=\{(a,r):Mar=Mm,\ Mr\ne Mm\},\\ C&=\{a:m\notin MaM\},\qquad \mathcal G=\{(a,r,b):m\in(MarM\cap MrbM)\setminus MarbM\}.\end{aligned}$$
--   Then for every word $x=x_1\cdots x_n\in M^*$ (of any length), $[x]=m$ if and only if
--
--   - (U) some prefix with product $r$ is followed by a letter $a$ with $(r,a)\in E$;
--   - (V) some suffix with product $r$ is preceded by a letter $a$ with $(a,r)\in F$;
--   - (C) no letter lies in $C$;
--   - (W) no infix $x_i\cdots x_j$ with $i<j$ has $x_i=a$, $[x_{i+1}\cdots x_{j-1}]=r$, $x_j=b$ with $(a,r,b)\in\mathcal G$ (with $r=1$ when $j=i+1$).
--
--   Furthermore, every $r$ occurring in $E$, $F$ or $\mathcal G$ satisfies $MmM\subsetneq MrM$, and in particular $\rho(r)<\rho(m)$.
--
--   This is the inductive step of the Aaronson–Grier–Schaeffer bound: membership in $P_m$ reduces to tests whose targets have strictly smaller rank.
--
--   **Formalization Note** Positions are 0-based; prefixes may be empty (product $1$), and so may the suffix in (V). Ideals are sets.
--
--   Differences from the source:
--
--   - encoding: 1-based positions x_1, …, x_n → 0-based list indices; prefix x.take i, suffix x.drop (i+1), infix (x.drop (i+1)).take (j−i−1); reason: same words and conditions
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 53 (Decomposition [Sch65, AGS19]), pp.69–70

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_Supplement_idealRank

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 53 (Decomposition [Sch65, AGS19]),
pp.69–70: "Let M be a finite aperiodic monoid and m ∈ M with ρ(m) > 0. Define
E = {(r, a) ∈ M × M : raM = mM, rM ≠ mM}, F = {(a, r) ∈ M × M : Mar = Mm, Mr ≠ Mm},
C = {a ∈ M : m ∉ MaM}, G = {(a, r, b) ∈ M × M × M : m ∈ (MarM ∩ MrbM) \ MarbM}. Then x ∈ P_m if
and only if all four of the following conditions hold: (U) some prefix x₁ ⋯ xᵢ with
[x₁ ⋯ xᵢ] = r is followed by the letter x_{i+1} = a, for some (r, a) ∈ E; (V) some suffix
x_j ⋯ x_n with [x_j ⋯ x_n] = r is preceded by the letter x_{j−1} = a, for some (a, r) ∈ F; (C) no
letter xᵢ belongs to C; (W) no infix xᵢ x_{i+1} ⋯ x_j with i < j has xᵢ = a, [x_{i+1} ⋯ x_{j−1}] = r,
and x_j = b for some (a, r, b) ∈ G (when j = i + 1 the infix product is r = 1). Furthermore, for
every r ∈ M appearing in E, F, or G we have MmM ⊊ MrM, and in particular ρ(r) < ρ(m)."
Here `P_m = {x ∈ M* : [x] = m}` (p.69). Two conjuncts: the equivalence for every word `x ∈ M*`
(any length, including the empty word), and the "Furthermore" clause.

**Formalization Note.** Words are lists; positions are `0`-based, so the paper's letter
`x_{i+1}` is `x[i]`, the prefix `x₁ ⋯ xᵢ` is `x.take i` (`0 ≤ i < n`, the empty prefix having
product `1`), the suffix after `x[i]` is `x.drop (i + 1)` (possibly empty), and the infix strictly
between `x[i]` and `x[j]` is `(x.drop (i + 1)).take (j - i - 1)` (empty when `j = i + 1`).
Ideals are sets: `sM = {s·c}`, `Ms = {c·s}`, `MsM = {a·s·b}`. `ρ` is `idealRank`. The set named
`G` here is the set of triples `Gt`, unrelated to an alphabet. -/
theorem theorem_53 :
    ∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], IsAperiodic M →
      ∀ m : M, 0 < idealRank m →
        let E : M → M → Prop := fun r a =>
          Set.range (fun c : M => r * a * c) = Set.range (fun c : M => m * c) ∧
            Set.range (fun c : M => r * c) ≠ Set.range (fun c : M => m * c)
        let F : M → M → Prop := fun a r =>
          Set.range (fun c : M => c * a * r) = Set.range (fun c : M => c * m) ∧
            Set.range (fun c : M => c * r) ≠ Set.range (fun c : M => c * m)
        let C : M → Prop := fun a => m ∉ {s : M | ∃ c d : M, c * a * d = s}
        let Gt : M → M → M → Prop := fun a r b =>
          m ∈ {s : M | ∃ c d : M, c * (a * r) * d = s} ∧
            m ∈ {s : M | ∃ c d : M, c * (r * b) * d = s} ∧
            m ∉ {s : M | ∃ c d : M, c * (a * r * b) * d = s}
        (∀ x : List M, x.prod = m ↔
          ((∃ (i : ℕ) (hi : i < x.length), E (x.take i).prod x[i]) ∧
           (∃ (i : ℕ) (hi : i < x.length), F x[i] (x.drop (i + 1)).prod) ∧
           (∀ a ∈ x, ¬ C a) ∧
           ¬ ∃ (i j : ℕ) (hi : i < x.length) (hj : j < x.length),
              i < j ∧ Gt x[i] ((x.drop (i + 1)).take (j - i - 1)).prod x[j])) ∧
        (∀ r : M, ((∃ a, E r a) ∨ (∃ a, F a r) ∨ (∃ a b, Gt a r b)) →
          {s : M | ∃ c d : M, c * m * d = s} ⊂ {s : M | ∃ c d : M, c * r * d = s} ∧
            idealRank r < idealRank m) := by sorry

end MonoidProdQ.Supplement
