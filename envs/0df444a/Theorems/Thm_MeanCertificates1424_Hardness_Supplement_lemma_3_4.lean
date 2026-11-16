-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_lemma_3_4
-- name    : MeanCertificates1424.Hardness.Supplement.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:56:28.845206+00:00
-- url     : https://prove2.me/theorems/3b08446e-c541-4d06-8ff5-5f399072f838
-- title:
--   Lemma 3.4 — zero-report endpoints and the diameter-two depth identity
-- statement:
--   Let $G$ be a connected graph on $n$ vertices, $L=1$, $\epsilon=0$, no audits, $b<n$ and uniform weights $w_v=1/n$. For $0\le m<n$ write $\Psi_G(m)=\max_{S\subseteq V,|S|\le m}\sum_{v\in S}d_G(v,V\setminus S)$.
--
--   1. At the zero report $y=0$,
--   $$u(0)=-\ell(0)=\frac{\Psi_G(b)}{n}.$$
--   2. If $G$ has diameter at most two and $m<n$, then
--   $$\Psi_G(m)=m+\max\{|X|:\ X\subseteq V,\ |N[X]|\le m\},$$
--   where $N[X]$ is the closed neighbourhood of $X$.
--
--   The lemma turns the zero-report endpoint into the combinatorial depth $\Psi_G$, the quantity whose hardness Theorems 3.5 and 3.7 establish.
--
--   **Formalization Note** $\Psi_G(b)$ is computed in $\mathbb N\cup\{\infty\}$ with $d_G(v,\emptyset)=+\infty$; the statement asserts it is finite and uses its natural value.
--
--   Differences from the source: none.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Lemma 3.4, printed p.9 (PDF p.11)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Complexity

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Lemma 3.4, printed p.9 / PDF p.11. `L = 1`, `ε = 0`, `Q = ∅`, `b < n`, `w_v = 1/n`.
(a) At the zero report `u(0) = −ℓ(0) = Ψ_G(b)/n`. (b) On graphs of diameter at most two,
for `m < n`, `Ψ_G(m) = m + max{|X| : X ⊆ V, |N[X]| ≤ m}`. -/
theorem lemma_3_4 (I : Inst) (hI : Valid I) (hL : I.lip = 1) (hε : I.noise = 0)
    (hQ : I.audits = ∅) (hb : I.budget < I.n) (hw : I.weights = uniformW I.n) :
    (I.reports = 0 →
      Psi I.graph I.budget ≠ ⊤ ∧
      upper I = ((((Psi I.graph I.budget).toNat : ℝ) / I.n : ℝ) : EReal) ∧
      lower I = ((-(((Psi I.graph I.budget).toNat : ℝ) / I.n) : ℝ) : EReal)) ∧
    (DiamLeTwo I.graph → ∀ m : ℕ, m < I.n →
      Psi I.graph m = ((m + (Finset.univ.filter fun X : Finset (Fin I.n) =>
        (closedNbhd I.graph X).card ≤ m).sup Finset.card : ℕ) : ℕ∞)) := by sorry

end MeanCertificates1424.Hardness.Supplement
