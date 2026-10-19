-- Prove2me | Theorems.Thm_OAI_FiniteCircle_excluded_character_branching
-- name    : OAI.FiniteCircle.excluded_character_branching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:50:32.5609+00:00
-- url     : https://prove2.me/theorems/8db22dd3-bb4e-4853-9df1-f13f1d758a9d
-- title:
--   Characters annihilating the excluded-coordinate cheap subgroup but not the global shift have frequency mass at least $(h/2)^h$
-- statement:
--   Let $h\ge2$ and $M\ge1$, and let $p_{l,k}$ ($l\in\mathbb{N}$, $0\le k<h$) be positive divisors of $M$ such that for every level $1\le l\le h$ the numbers $p_{l,0},\dots,p_{l,h-1}$ are pairwise distinct primes, each at least $h^3$. For a divisor $p$ of $M$ let $\iota_p:\mathbb{Z}/p\to\mathbb{Z}/M$, $a\mapsto(M/p)\,a$. For $y\in\mathbb{Z}/M$ let $|y|_M\in\{0,\dots,\lfloor M/2\rfloor\}$ be the absolute value of its representative in $(-M/2,M/2]$. For a finite set $\Lambda$, every additive character $\chi$ of $(\mathbb{Z}/M)^{\Lambda}$ (a homomorphism into the multiplicative group of $\mathbb{C}$) has frequencies $\xi_\lambda\in\mathbb{Z}/M$, $\lambda\in\Lambda$, determined by $\chi(a\,e_\lambda)=e^{2\pi\mathrm{i}\,\xi_\lambda a/M}$ for all $a\in\mathbb{Z}/M$, where $e_\lambda$ is the standard basis vector.
--
--   *Tree and cheap subgroup.* Let $\Lambda_0$ be a single point and $\Lambda_l=\{0,\dots,h-1\}\times\Lambda_{l-1}$; so $\Lambda_h$ is the set of leaves of the complete $h$-ary rooted tree of depth $h$. For $z\in\prod_{k<h}\mathbb{Z}/p_{l,k}$ define $\sigma_l(z)\in(\mathbb{Z}/M)^{h}$ by
--
--   $$
--   \sigma_l(z)_i=\sum_{j\ne i}\iota_{p_{l,j}}(z_j)\qquad(0\le i<h),
--   $$
--
--   the sum running over $0\le j<h$, $j\ne i$. The cheap subgroups $C_l\le(\mathbb{Z}/M)^{\Lambda_l}$ are $C_0=\{0\}$ and, for $l\ge1$, the set of vectors $v$ for which there exist $z\in\prod_{k<h}\mathbb{Z}/p_{l,k}$ and elements $c_i\in C_{l-1}$ ($0\le i<h$) with $v(i,\lambda)=c_i(\lambda)+\sigma_l(z)_i$ for all $(i,\lambda)\in\{0,\dots,h-1\}\times\Lambda_{l-1}$.
--
--   **Theorem.** Let $\chi$ be an additive character of $(\mathbb{Z}/M)^{\Lambda_h}$ that is trivial on $C_h$, and let $\theta\in\mathbb{Z}/M$ be such that $\chi(\theta,\theta,\dots,\theta)\ne1$. Then
--
--   $$
--   \sum_{\lambda\in\Lambda_h}|\xi_\lambda|_M\ \ge\ \Big(\frac h2\Big)^{h}.
--   $$
--
--   So any character that sees the global constant shift but is blind to all cheap moves must have large $\ell^1$ frequency mass. This is the annihilator hypothesis of the weighted $\ell^1$ displacement inequality, with $B=(h/2)^h$, $H=C_h$ and $w$ the constant vector $\theta$, in the distortion lower bound for the excluded-coordinate circle words.
--
--   **Formalization Note** $\Lambda_h$ is `TreeLeaf (fun _ => Fin h) h`, $C_h$ is `excludedCheap h p M hd h` (built from `treeCheap` and `excludedPhaseHom`), $\xi_\lambda$ is `coordinateFrequency χ λ` and $|\xi_\lambda|_M$ is its `valMinAbs.natAbs`; triviality on $C_h$ is `χ.compAddMonoidHom (excludedCheap h p M hd h).subtype = 0`. No distinctness of primes across different levels is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/TreeBranching.lean#L474-L503

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.excluded_character_branching {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hh : 2 ≤ h) (hd : ∀ l (k : Fin h), p l k ∣ M)
    (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (χ : AddChar (TreeLeaf (fun _ => Fin h) h → ZMod M) ℂ)
    (ha : χ.compAddMonoidHom (excludedCheap h p M hd h).subtype = 0)
    (θ : ZMod M) (hw : χ (fun _ => θ) ≠ 1) :
    ((h:ℝ)/2)^h ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ) := by sorry
