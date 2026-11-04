-- Prove2me | Theorems.Thm_OAI_SignedSweeps_occupied_sweep_trace_bound
-- name    : OAI.SignedSweeps.occupied_sweep_trace_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-03T23:35:59.942254+00:00
-- url     : https://prove2.me/theorems/7eb56a25-5e97-4f36-a162-c0dac0acb19c
-- title:
--   Trace bound for fixed marks in a signed sweep step
-- statement:
--   This is the bound at a fixed assignment of marks in one step of the signed sweep moment induction.
--
--   Throughout, $S_p$ acts on the word space $W_p=\ell^2\big((C\sqcup C)^p\big)$, with $C=\{1,\dots,q\}$ two-coloured into even and odd letters, by the signed action $(\rho(g)f)(w)=\varepsilon(g,w)\,f(w\circ g)$, where $\varepsilon(g,w)$ is the sign of the permutation $g$ induces between the odd positions of $w$. For $u+v=p$ and partitions $\alpha\vdash u$, $\beta\vdash v$, the operator $P_{\alpha,\beta}$ is the sum, over the placements of $u$ even sites among the $p$ sites, of the tensor product of the orthogonal projections onto the $S^\alpha$-isotypic part of the $u$ even sites and the $S^\beta$-isotypic part of the $v$ odd sites. Its entropy is $F(\alpha,\beta)=\sum_{a\in\alpha\cup\beta}a\log\frac{u+v}{a}$, and a *local type* on $k$ sites is such a pair of total size $k$. For an enumeration $e$ of the $p$ sites by blocks $j\in J$ with $k_j$ sites each and local types $t=(t_j)_j$, $P^{e}_{t}$ is the corresponding tensor product of local type projections, with $F(t)=\sum_jF(t_j)$. For a coefficient function $f:G\to\mathbb{C}$ on a finite group and a representation $\pi$, $\pi(f)=\sum_gf(g)\pi(g)$.
--
--   Let $n=2^{a+b}$, identified with the rectangle $2^a\times2^b$ through the binary coordinates, let $p+l=n$, let $z$ be an injection of $l$ marks into the $n$ positions and $\iota$ an enumeration of the other $p$ positions, and let $0\le\eta\le1$, $\tau\in\mathbb{R}$, $q>0$, $j\in\mathbb{N}$, $R\ge2\max(2^a,2^b)+2q+1$. Write $J_r(\lambda)=\dim S^\lambda\operatorname{Re}\operatorname{Tr}_{S^\lambda}\big((T^*T)^r\big)$ for the weighted moment of the $d$-coordinate sweep $T$, and
--
--   $$
--   g_\tau(t,h)=\max\{0,\ \tau h\log t-h\log(t/h)\}.
--   $$
--
--   Assume that for $d\in\{a,b\}$ and every signed occurrence of $(\alpha,\beta,\gamma)$ in $\lambda\vdash2^d$ one has $J_{2^j}(\lambda)\le\exp(\eta F(\alpha,\beta)+g_\tau(2^d,|\gamma|))$. Let $c,c'$ be the coefficients on $S_{2^{a+b}}$ of the $2^j$-th powers of the positive squares of the products of column sweeps and of row sweeps, and let $c_z,c'_z$ be their restrictions to $S_p$ along $\iota$. Then for $u+v=p$, $\alpha\vdash u$, $\beta\vdash v$ with at most $q$ rows,
--
--   $$
--   \operatorname{Re}\operatorname{Tr}_{W_p}\big(P_{\alpha,\beta}\,\rho(c_z)\,\rho(c'_z)\big)\le\Phi(z)\exp\Big(\Gamma_\tau(z)+(\eta-1)F(\alpha,\beta)+l+2^bE(2^a,q,R)+2^aE(2^b,q,R)\Big).
--   $$
--
--   Here, with $h_j$ marks in column $j$ and $b_i$ marks in row $i$, $\Phi(z)=\prod_j(2^a)_{h_j}^{-1}\prod_i(2^b)_{b_i}^{-1}$ is the product of inverse falling factorials, $\Gamma_\tau(z)=\sum_jg_\tau(2^a,h_j)+\sum_ig_\tau(2^b,b_i)$, and
--
--   $$
--   E(t,q,R)=E_{\mathrm{loc}}(t,q,R)+\big(4\lfloor\sqrt t\rfloor+1\big)\log R+2q^2\log R,
--   $$
--
--   where $E_{\mathrm{loc}}(t,q,R)=\big(2\lfloor\sqrt t\rfloor+26q^2+8q+1\big)\log R+8q+1$.
--
--   The bound is what remains to be summed over mark assignments in the induction step.
--
--   **Formalization Note** The upstream statement is reproduced verbatim from `OccupiedSweep.lean`; columns are indexed by $2^b$ and rows by $2^a$ through `sweepBoard`.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 4, eqs. (21)-(26). Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/OccupiedSweep.lean#L79-L194

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs

open scoped BigOperators Classical

theorem OAI.SignedSweeps.occupied_sweep_trace_bound {a b j q R p l : ℕ} (hq : 0 < q)
    (hn : p+l=2^(a+b)) (z : MarkedAssignment l (2^(a+b)))
    {η τ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1)
    (HA : ∀ (lam : Partition (2^a)) (u v l : ℕ) (h : u+v+l=2^a)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^a) l))
    (HB : ∀ (lam : Partition (2^b)) (u v l : ℕ) (h : u+v+l=2^b)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^b) l))
    (hR : 2*max (2^a) (2^b)+2*q+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (pairTypeProjection h α β (Fin q) *
        coefficientAction (signedWordRepresentation p (Fin q))
          (fun g => columnPowerCoefficient a b (2^j) (g.viaEmbedding (markedInjection hn z))) *
        coefficientAction (signedWordRepresentation p (Fin q))
          (fun g => rowPowerCoefficient a b (2^j) (g.viaEmbedding (markedInjection hn z))))).re ≤
      holePrefactor (markedBoardPlacement (sweepBoard a b) z) *
      Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1+
        (η-1)*signedEntropy α β+l+(2^b : ℕ)*typedLineError (2^a) q R+
        (2^a : ℕ)*typedLineError (2^b) q R) := by sorry
