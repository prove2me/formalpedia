-- Prove2me | Theorems.Thm_OAI_Erdos3_CylinderRemovalChain_shell_prefactor_le_exp
-- name    : OAI.Erdos3.CylinderRemovalChain.shell_prefactor_le_exp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:22:12.978569+00:00
-- url     : https://prove2.me/theorems/6ca32f74-3def-4d59-a9e7-f3965eb16a0a
-- title:
--   The shell prefactor sum over a cylinder removal chain is at most an explicit exponential
-- statement:
--   Let $\Omega$ and $\iota$ be finite types ($\iota$ with decidable equality), and $X,Y : \iota\to$ types, each $X_i$ finite with decidable equality and each $Y_i$ finite. Let $\mu_i$ be a `FiniteProbabilityWeights (X i)` for each $i$ (a `FiniteProbabilityWeights` bundles nonnegative weights summing to $1$), $\mathrm{base}\in\prod_i X_i$, $p$ a `FiniteProbabilityWeights Ω`, and $F : \Omega\to\prod_i X_i$. Let $K,\tau,\eta,P,S,V,\mathrm{level},v,\varepsilon,L,T$ be real numbers, $j,r$ natural numbers, $w,\mathrm{rem} : \Omega\to\mathbb{R}$, and $cs$ a list of `ProductCylinder X` (a `ProductCylinder X` is a pair $(S,a)$ of a finite set $S\subseteq\iota$ and an assignment $a\in\prod_{i\in S}X_i$). Assume:
--
--   - `CylinderRemovalChain μ base p F K τ j r w rem cs`: the inductive predicate saying that removing the cylinders of $cs$ in order from the weight $w$ (each removal sets the weight to $0$ on those $z$ with $F(z)$ in the cylinder) ends at $\mathrm{rem}$, where each cylinder $c=(S,a)$ removed has $|S|\le j$, `c.mass` of the current `observedProductDensity` greater than $\tau$, and its normalized section satisfying OpenAI's `ProductBoundedMarginals … K r`;
--   - $(\mu_i).\mathrm{weight}(x)>0$ for all $i$ and $x$; $0\le w(z)\le 1$ for all $z$;
--   - $0<\tau\le 1$ and $\eta\le 1$;
--   - `ProductMarginalsClose μ (observedProductDensity μ p F 1) η j`: for every $B\subseteq\iota$ with $|B|\le j$ and every $x$ of positive product weight, OpenAI's `productConditionalMean μ B` of the density `observedProductDensity μ p F 1` at $x$ (its mean over the coordinates outside $B$ with those in $B$ fixed to $x$) is within $\eta$ of $1$ (`observedProductDensity μ p F f` is the density, with respect to the product of the $\mu_i$, of the push-forward under $F$ of $f\cdot p$);
--   - $0\le P$, $0\le S$, $0\le V$, $|\iota|\le e^P$, $|X_i|\le e^S$ and $|Y_i|\le e^V$ for all $i$;
--   - $0\le\mathrm{level}\le 2$, $0\le v\le 1$, $0\le\varepsilon$, and $\tau^{-1}\le e^T$.
--
--   Pair each cylinder $c=(S_c,a_c)$ of $cs$ with the corresponding entry $f_c$ of `removedCylinderWeights F w cs` (the part of the running weight that is cut off by $c$ at its removal step). Then
--   $$\sum_{c\in cs}\Big(\prod_{i\in S_c}|Y_i|\Big)\cdot m_c\cdot\mathrm{level}\cdot(v+\tau)(6+2\varepsilon)\,2^{|S_c|}\,(3\tau^{-1})\,\big(3e^{L+T}\big)\le\exp\big(j(P+S+V+2)+\varepsilon+L+2T+10\big),$$
--   where $m_c$ is `c.mass μ base (observedProductDensity μ p F f_c)`, the mean of that density, under the product of the $\mu_i$, over the coordinates outside $S_c$ with the coordinates in $S_c$ fixed to $a_c$ (OpenAI's `productConditionalMean μ S_c` at the point that agrees with $a_c$ on $S_c$ and with $\mathrm{base}$ elsewhere).
--
--   Lean: `OAI.Erdos3.CylinderRemovalChain.shell_prefactor_le_exp` in `lean/OAI/Combinatorics/Progressions/Dynamics/CylinderShellCountBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B011` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/CylinderShellCountBudget.lean#L88

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B011

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem CylinderRemovalChain.shell_prefactor_le_exp {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ η P S V level v ε L T : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : η ≤ 1)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η j)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp S)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp V)
    (hl0 : 0 ≤ level) (hl2 : level ≤ 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hε : 0 ≤ ε)
    (hτinv : τ⁻¹ ≤ Real.exp T) :
    ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, Y i.val) : ℝ) *
        (cf.1.mass μ base (observedProductDensity μ p F cf.2) * level * (v + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))).sum ≤
      Real.exp ((j : ℝ) * (P + S + V + 2) + ε + L + 2 * T + 10) := by
  sorry

end Erdos3
end
end OAI
