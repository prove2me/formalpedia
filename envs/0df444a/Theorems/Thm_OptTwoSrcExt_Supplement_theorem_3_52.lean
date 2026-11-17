-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_3_52
-- name    : OptTwoSrcExt.Supplement.theorem_3_52
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:40:11.824538+00:00
-- url     : https://prove2.me/theorems/86881e13-1404-4c29-9d31-24edbebcbe40
-- title:
--   Theorem 3.52 — fixed-deficiency arbitrary rank margin for a tagged evaluator
-- statement:
--   Let $A_*\ge1$ be the absolute integer of Lemma 3.39, $N=A_*s$, $L=\mathbb F_{2^N}$ and $F=\mathbb F_{2^s}$. There is a fixed $\tau_*>0$ such that, for every prescribed constant $K>0$, there are explicit constants $J,c$ and an explicit evaluator $E_a(x,y)\in F$ (inputs $x,y\in L$, tag $a\in F$; every element of $F$ is an allowed tag) with the following properties for all sufficiently large $N=A_*s$:
--
--   1. for all $A,B\subseteq L$ of size at least $2^{(1-\tau_*)N}$, all arbitrary maps $f,g:L\to L$, all distinct tags $a\ne a'$ and all $\lambda\in F^\times$, $\mu\in F$,
--   $$\mathrm{rank}_2\Big[\mathrm{Tr}_{F/\mathbb F_2}\big(\lambda E_a(x,y)+\mu E_{a'}(f(x),g(y))\big)\Big]_{A\times B}>KN;\tag{3.58}$$
--   2. each character $\mathrm{Tr}_{F/\mathbb F_2}(\lambda E_a)$, $\lambda\in F^\times$, has global rank (on $L\times L$) at most $(c+1)N+Js$.
--
--   The deficiency $\tau_*$ is independent of $K$, while the evaluator and its rank upper bound depend on $K$. Large mixed rank on every dense rectangle against every tampered comparison is what lets the tagged rows of the non-malleable construction stay fresh.
--
--   **Formalization Note** $A_*$ is quantified existentially before $\tau_*$; $J$, $c$, the evaluator and the length threshold are chosen after $K$. "Explicit evaluator" is one `LowErrExt.IsPolyTime` machine for all $s$, outputting exactly $s$ bits on $[x,y,a]$; field elements of $F$ are written in the power basis of the explicit `BinField`. The field structure of $L$ does not enter the statement ($f,g$ are arbitrary maps and the ranks are those of $0/1$ tables), so $L$ is represented by its binary identification $\mathbb F_2^N$. The decomposition $E_a=G_c+T_a$ of (3.57) names the construction and adds no condition.
--
--   Differences from the source:
--   - encoding: L = F_{2^N} ⊇ F = F_{2^s}; an evaluator E_a = G_c + T_a with explicit constants → x, y ∈ 𝔽₂^N (bit vectors), F the explicit BinField Pm s; one IsPolyTime machine Em with E_a(x, y) read from Em [x, y, a]; reason: the statement only involves the 0/1 tables of the characters and arbitrary maps f, g, so the field structure of L and the form G_c + T_a add no condition
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.52, p.61 (PDF p.63); Lemma 3.39, p.52 (PDF p.54)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_rank2
import Definitions.Def_OptTwoSrcExt_machineVec
import Definitions.Def_OptTwoSrcExt_Supplement_BinField

open LowErrExt OptTwoSrcExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 3.52 (Fixed-deficiency arbitrary rank margin).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.52, printed p.61 (PDF p.63): "There is a fixed
τ∗ > 0 such that, for every prescribed constant K > 0, explicit constants J, c and an evaluator
Ea(x, y) = Gc(x, y) + Ta(x, y) ∈ F (3.57) have the following properties for all sufficiently large
N = A∗s. For all A, B ⊆ L of size at least 2^{(1−τ∗)N}, all arbitrary maps f, g : L → L, all
allowed distinct fixed tags a, a′, and all λ ∈ F^×, µ ∈ F,
rank2[Tr_{F/F2}(λEa(x, y) + µEa′(f(x), g(y)))]_{A×B} > KN. (3.58)
Each character of Ea has global rank at most (c + 1)N + Js = OK(N). The entropy deficiency τ∗ is
independent of K, although the evaluator and its rank upper bound depend on K."
Lemma 3.39, printed p.52 (PDF p.54): "There is an absolute integer A∗ ⩾ 1 such that, for N = A∗s and
F = F_{2^s} … Every field element is an allowed tag."

There are an integer `A∗ ≥ 1` and `τ∗ > 0` such that for every `K > 0` there are integers `J, c`,
polynomial-time machines `Em` (the evaluator) and `Pm` (field construction) and a threshold `s₀` such
that for every `s ≥ s₀`, with `N = A∗s`, `L = 𝔽₂^N` (the inputs, as bit vectors) and `F = 𝔽_{2^s}`
(the explicit field `BinField Pm s`): `Pm` constructs `F`, `Em` outputs exactly `s` bits on
`[x, y, a]` (`x, y ∈ L`, tag `a ∈ F`), and, writing `E_a(x, y) ∈ F` for that output,
1. for all `A, B ⊆ L` with `|A|, |B| ≥ 2^{(1−τ∗)N}`, all maps `f, g : L → L`, all tags `a ≠ a'` in
   `F` and all `λ ∈ F^×`, `μ ∈ F`, the `A × B` matrix `Tr_{F/𝔽₂}(λE_a(x, y) + μE_{a'}(f(x), g(y)))`
   has `𝔽₂`-rank `> KN`;
2. for every tag `a` and every `λ ∈ F^×`, the `L × L` matrix `Tr_{F/𝔽₂}(λE_a(x, y))` has `𝔽₂`-rank
   at most `(c + 1)N + Js`.

**Formalization Note.** `A∗` is the absolute integer of Lemma 3.39, quantified existentially before
`τ∗`; `τ∗` is chosen before `K`, and `J, c`, the evaluator and the length threshold after `K`.
"Explicit evaluator" is one `LowErrExt.IsPolyTime` machine for all `s`; field elements are written in
the power basis of the explicit field `BinField Pm s` (`eltBits`, `eltOfBits`). The field structure of
`L = 𝔽_{2^N}` and the inclusion `F ⊆ L` do not enter the statement (`f, g` are arbitrary maps and the
ranks are those of `0/1` tables), so `L` is its binary identification `𝔽₂^N`. The decomposition
`E_a = G_c + T_a` names the construction and adds no condition. Every element of `F` is an allowed
tag. -/
theorem theorem_3_52 :
    ∃ As : ℕ, 1 ≤ As ∧ ∃ τ : ℝ, 0 < τ ∧ ∀ K : ℝ, 0 < K →
      ∃ J c : ℕ, ∃ Em Pm : List (List Bool) → List Bool, IsPolyTime Em ∧ IsPolyTime Pm ∧
        ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → IsFieldPolyAt Pm s ∧
          (∀ (x y : Fin (As * s) → ZMod 2) (a : BinField Pm s),
            (Em [bitsOfVec x, bitsOfVec y, eltBits Pm s a]).length = s) ∧
          (∀ (A B : Finset (Fin (As * s) → ZMod 2)),
            (2 : ℝ) ^ ((1 - τ) * (As * s : ℕ)) ≤ A.card →
            (2 : ℝ) ^ ((1 - τ) * (As * s : ℕ)) ≤ B.card →
            ∀ (f g : (Fin (As * s) → ZMod 2) → (Fin (As * s) → ZMod 2)) (a a' : BinField Pm s),
              a ≠ a' → ∀ l μ : BinField Pm s, l ≠ 0 →
                K * (As * s : ℕ) < (rank2 (fun (x : A) (y : B) =>
                  absTr Pm s (l * eltOfBits Pm s (Em [bitsOfVec (x : Fin (As * s) → ZMod 2),
                      bitsOfVec (y : Fin (As * s) → ZMod 2), eltBits Pm s a]) +
                    μ * eltOfBits Pm s (Em [bitsOfVec (f x), bitsOfVec (g y),
                      eltBits Pm s a']))) : ℝ)) ∧
          ∀ (a l : BinField Pm s), l ≠ 0 →
            rank2 (fun x y : Fin (As * s) → ZMod 2 =>
              absTr Pm s (l * eltOfBits Pm s (Em [bitsOfVec x, bitsOfVec y, eltBits Pm s a]))) ≤
              (c + 1) * (As * s) + J * s := by sorry

end OptTwoSrcExt.Supplement
