-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_kl_chain_rule_le
-- name    : FoundationsRL.DECLower.kl_chain_rule_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:16:04.209664+00:00
-- url     : https://prove2.me/theorems/7c048701-c372-4cc0-988d-ec69cb3f6874
-- title:
--   Lemma 22 — chain rule for KL divergence, $\le$ on general spaces (corrected: "=" fails on general measurable spaces)
-- statement:
--   Let $(\mathcal X_k,\mathcal F_k)_{k\ge 0}$ be measurable spaces, $x_0\in\mathcal X_0$ an initial point, and for each $k$ let $\kappa_k,\eta_k$ be probability kernels from $\mathcal X_0\times\dots\times\mathcal X_k$ to $\mathcal X_{k+1}$. Let $P$ and $Q$ be the laws of $(x_0,X_1,\dots,X_n)$ under $X_i\sim\kappa_{i-1}(\cdot\mid x_0,X_{1:i-1})$ and $X_i\sim\eta_{i-1}(\cdot\mid x_0,X_{1:i-1})$ respectively. If each map $y\mapsto D_{\mathrm{KL}}(\kappa_k(\cdot\mid y)\,\|\,\eta_k(\cdot\mid y))$, $k<n$, is measurable, then
--
--   $$
--   D_{\mathrm{KL}}(P\,\|\,Q)\le\mathbb E_P\left[\sum_{i=1}^n D_{\mathrm{KL}}\bigl(\kappa_{i-1}(\cdot\mid x_0,X_{1:i-1})\,\big\|\,\eta_{i-1}(\cdot\mid x_0,X_{1:i-1})\bigr)\right].
--   $$
--
--   This is the direction of the chain rule used to bound the KL divergence between the laws of two interaction histories in the proof of Proposition 28. The equality holds when the spaces are standard Borel (the companion milestone).
--
--   Differences from the source:
--   - correction: $D_{\mathrm{KL}}(P\|Q)=\mathbb E_P[\sum_i D_{\mathrm{KL}}(P_i\|Q_i)]$ on arbitrary measurable spaces → $\le$; reason: the equality is false: $\mathcal X_1=[0,1]$ Borel with Lebesgue law under both, $\mathcal X_2=[0,1]$ with the countable–cocountable σ-algebra, $P_2(\cdot\mid x)=\delta_x$, $Q_2(\cdot\mid x)=\nu$ ($\nu(B)=1$ iff $B$ cocountable); both joint laws equal $A\times B\mapsto\mathrm{Leb}(A)\mathbf 1[B\text{ cocountable}]$, so the left side is $0$ while every conditional KL is $+\infty$
--   - reading: $\mathcal X^i=\prod_{i=t}\mathcal X_t$ → $\prod_{t=1}^i\mathcal X_t$; reason: index typo in the PDF, $\mathcal F^i=\bigotimes_{t=1}^i\mathcal F_t$ on the same line fixes the reading
--   - generalization: kernels from $\mathcal X^{i-1}$ with $\mathcal X^0$ a point → kernels that may also depend on a fixed initial point $x_0\in\mathcal X_0$; reason: $\mathcal X_0$ a one-point space is exactly the notes' case
--   - reading: $\mathbb E_P[\cdot]$ of the conditional KL sum → a Lebesgue integral with each conditional KL map assumed measurable; reason: the expectation presupposes measurability; without it a Lebesgue integral is a lower integral
--   - encoding: $n$ spaces and kernels → families indexed by all of $\mathbb N$, of which only the first $n$ kernels enter; KL divergence valued in $[0,\infty]$; reason: Lean convention; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 22, (6.35), p. 107

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_seqLaw
import Definitions.Def_FoundationsRL_DECLower_condKLSum

open MeasureTheory ProbabilityTheory InformationTheory Finset Preorder
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Lemma 22 (Chain rule for KL divergence), inequality form on general measurable spaces.**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 22, (6.35), p. 107.

For two families of probability kernels `κ, η` with sequential laws `P = seqLaw κ n x₀` and
`Q = seqLaw η n x₀`, whose conditional KL divergences `y ↦ D_KL(κ k y ∥ η k y)` are measurable for
`k < n`: `D_KL(P ∥ Q) ≤ E_P[Σ_{i=1}^n D_KL(P_i(· | X_{1:i−1}) ∥ Q_i(· | X_{1:i−1}))]`.

**Formalization Note.** *Correction*: the notes print "=". On general measurable spaces the
equality fails: with `X_1 = [0,1]` (Borel, Lebesgue under both laws), `X_2 = [0,1]` with the
countable–cocountable σ-algebra, `P_2(·|x) = δ_x` and `Q_2(·|x) = ν` (`ν(B) = 1` iff `B` is
cocountable), both joint laws are `A × B ↦ Leb(A)·1[B cocountable]`, so `D_KL(P ∥ Q) = 0`, while
`D_KL(δ_x ∥ ν) = ∞` for every `x`. The equality under standard Borel spaces is
`kl_chain_rule_eq_of_standardBorel`. The measurability hypothesis is presupposed by the
expectation in (6.35). The PDF's `X^i = Π_{i=t} X_t` is read `Π_{t=1}^i X_t`. Coordinate `0` is a
common initial point (`X 0 = PUnit` is the paper's case). -/
theorem kl_chain_rule_le {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (x₀ : Π i : Iic 0, X i) (n : ℕ)
    (hmeas : ∀ k < n, Measurable (fun y => klDiv (κ k y) (η k y))) :
    klDiv (seqLaw κ n x₀) (seqLaw η n x₀)
      ≤ ∫⁻ x, condKLSum κ η n x ∂(seqLaw κ n x₀) := by sorry

end FoundationsRL.DECLower
