-- Prove2me | Theorems.Thm_OAI_SignedSweeps_signed_sweep_recurrence
-- name    : OAI.SignedSweeps.signed_sweep_recurrence
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-03T23:35:51.908295+00:00
-- url     : https://prove2.me/theorems/6644b5e9-9966-408e-9e53-aab3c415eb93
-- title:
--   Recurrence for signed sweep moments along a coordinate split
-- statement:
--   This is the moment recurrence along a split of the coordinates: it bounds a weighted sweep moment on $2^{a+b}$ cards by the corresponding bounds on $2^a$ and $2^b$ cards, for every prescribed signed occurrence.
--
--   Let $T_\lambda$ be the sweep operator on the Specht module $S^\lambda$, $\lambda\vdash2^d$, and $J_r(\lambda)=\dim S^\lambda\operatorname{Re}\operatorname{Tr}_{S^\lambda}\big((T_\lambda^*T_\lambda)^r\big)$. A *signed occurrence* of $(\alpha,\beta,\gamma)$ in $\lambda$ is an injective $S_u\times S_v\times S_l$-equivariant map $S^\alpha\otimes S^{\beta^t}\otimes S^\gamma\to S^\lambda$. Put $F(\alpha,\beta)=\sum_{x\in\alpha\cup\beta}x\log\frac{u+v}{x}$ and
--
--   $$
--   g_\tau(t,h)=\max\{0,\ \tau h\log t-h\log(t/h)\}.
--   $$
--
--   Let $0\le\eta\le1$, $0\le\kappa\le\tau$, $q>0$, $R\ge2\max(2^a,2^b)+2q+1$, and $j\in\mathbb{N}$. Assume that for $d\in\{a,b\}$ every signed occurrence in $\lambda\vdash2^d$ satisfies $J_{2^j}(\lambda)\le\exp(\eta F(\alpha,\beta)+g_\tau(2^d,|\gamma|))$. Then for $n=2^{a+b}$ and every signed occurrence of $(\alpha,\beta,\gamma)$ in $\lambda\vdash n$, $|\gamma|=l$, where $\alpha,\beta$ have at most $q$ rows,
--
--   $$
--   J_{2^j}(\lambda)\le\exp\Big(\eta F(\alpha,\beta)+\tau l\log n-l\log(n/l)+6l+2^bE(2^a,q,R)+2^aE(2^b,q,R)+C_\kappa(2^a,2^b)+(2^a+2^b)\log(l+1)\Big),
--   $$
--
--   where $C_\kappa(s,m)=ms^{1-\kappa}\log s+sm^{1-\kappa}\log m$ and
--
--   $$
--   E(t,q,R)=\big(2\lfloor\sqrt t\rfloor+26q^2+8q+1\big)\log R+8q+1+\big(4\lfloor\sqrt t\rfloor+1\big)\log R+2q^2\log R.
--   $$
--
--   With a balanced split, this is the induction step of the every-occurrence moment bound, Theorem 1.1 of the source.
--
--   **Formalization Note** The upstream statement is reproduced verbatim from `SweepRecurrence.lean`.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 4, eqs. (19)-(29). Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/SweepRecurrence.lean#L28-L115

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs

open scoped BigOperators Classical

theorem OAI.SignedSweeps.signed_sweep_recurrence {a b j q R : ℕ} (hq : 0 < q)
    {η τ κ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    (HA : ∀ (lam : Partition (2^a)) (u v l : ℕ) (h : u+v+l=2^a)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^a) l))
    (HB : ∀ (lam : Partition (2^b)) (u v l : ℕ) (h : u+v+l=2^b)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^b) l))
    (hR : 2*max (2^a) (2^b)+2*q+1 ≤ R)
    (lam : Partition (2^(a+b))) (u v l : ℕ) (h : u+v+l=2^(a+b))
    (α : Partition u) (β : Partition v) (γ : Partition l)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (ho : SignedOccurrence h α β γ lam) :
    weightedMoment lam (2^j) ≤ Real.exp (η*signedEntropy α β+
      τ*l*Real.log (2^(a+b) : ℕ)-(l:ℝ)*Real.log ((2^(a+b) : ℕ)/ (l:ℝ))+6*l+
      (2^b : ℕ)*typedLineError (2^a) q R+(2^a : ℕ)*typedLineError (2^b) q R+
      holeClippingError κ (2^a) (2^b)+((2^a : ℕ)+(2^b : ℕ) : ℝ)*Real.log (l+1)) := by sorry
