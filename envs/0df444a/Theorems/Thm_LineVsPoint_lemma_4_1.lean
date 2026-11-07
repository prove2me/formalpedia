-- Prove2me | Theorems.Thm_LineVsPoint_lemma_4_1
-- name    : LineVsPoint.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:51.698687+00:00
-- url     : https://prove2.me/theorems/254ce097-3b88-4856-b21b-ab12fc80263c
-- title:
--   Lemma 4.1 — sampler estimates for the affine Grassmann graph
-- statement:
--   **Lemma 4.1.** Let $\mathbb F_q$ be a finite field and $m\ge3$ (and $q\ge2$). Write $\mathcal L_{q,m}$ for the lines and $\mathcal P_{m,q}$ for the planes of $\mathbb F_q^m$.
--
--   1. If $a:\mathcal L_{q,m}\to[0,1]$, $\bar a=\mathbb E_L[a(L)]$ and $a(P)=\mathbb E_{L\subseteq P}[a(L)]$, then $\mathbb E_P\bigl[(a(P)-\bar a)^2\bigr]\le 4/q$.
--   2. If $\mathcal B\subseteq\mathcal P_{m,q}$ and $X\subseteq\mathbb F_q^m$, then
--   $$
--   \Bigl|\Pr_{P\in\mathcal P_{m,q},\,x\in P}[P\in\mathcal B,\ x\in X]-\mu(\mathcal B)\mu(X)\Bigr|\le\frac2q\sqrt{\mu(\mathcal B)\mu(X)} .
--   $$
--   3. Fix $x\in\mathbb F_q^m$, let $\mathcal P_x=\{P\in\mathcal P_{m,q}:x\in P\}$, and let $G_x$ be the uniform edge distribution on the graph on $\mathcal P_x$ in which $P$ and $P'$ are adjacent when $P\cap P'$ is a line. If $\mathcal B_1,\mathcal B_2\subseteq\mathcal P_x$ and $\mu_x$ is the uniform density in $\mathcal P_x$, then
--   $$
--   \Bigl|\Pr_{(P,P')\sim G_x}[P\in\mathcal B_1,\ P'\in\mathcal B_2]-\mu_x(\mathcal B_1)\mu_x(\mathcal B_2)\Bigr|\le\frac1q\sqrt{\mu_x(\mathcal B_1)\mu_x(\mathcal B_2)} .
--   $$
--
--   All expectations and probabilities are uniform over lines, planes and points. Part (iii) is cited from [BR26, Claim 5]. These estimates drive the reduction from dimension $m$ to planes in Section 4.
--
--   Differences from the source:
--   - encoding: q ≥ 2 → no hypothesis; reason: every finite field has at least two elements
--   - encoding: expectations E_L, E_{L⊆P}, E_P and Pr_{(P,P′)∼G_x} → uniform averages over Line F m, the lines contained in P, Plane F m, and the ordered pairs of planes through x meeting in a line; reason: the paper's distributions are uniform over these finite sets
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 4.1, p.17

import Definitions.Def_LineVsPoint_flatIncProb
import Definitions.Def_LineVsPoint_accPVP

set_option autoImplicit false

universe u

namespace LineVsPoint

open Classical in
/-- **Lemma 4.1** (sampler estimates for affine Grassmann graphs). *For `m ≥ 3` and `q ≥ 2`, the
following hold. (i) If `a : L_{q,m} → [0, 1]`, `ā = E_L[a(L)]`, and `a(P) = E_{L⊆P}[a(L)]`, then
`E_P[(a(P) − ā)²] ≤ 4/q`. (ii) If `B ⊆ P_{m,q}` and `X ⊆ F^m_q`, then
`|Pr_{P∈P_{m,q}, x∈P}[P ∈ B, x ∈ X] − µ(B)µ(X)| ≤ (2/q)√(µ(B)µ(X))`. (iii) Fix `x ∈ F^m_q`, let
`P_x := {P ∈ P_{m,q} : x ∈ P}`, and let `G_x` be the uniform edge distribution on the graph on
`P_x` in which `P` and `P′` are adjacent when `P ∩ P′` is a line. If `B_1, B_2 ⊆ P_x`, and `µ_x`
denotes uniform density in `P_x`, then
`|Pr_{(P,P′)∼G_x}[P ∈ B_1, P′ ∈ B_2] − µ_x(B_1)µ_x(B_2)| ≤ (1/q)√(µ_x(B_1)µ_x(B_2))`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Lemma 4.1, p.17.

**Formalization Note.** `q = |F| ≥ 2` holds for every finite field. All expectations and
probabilities are uniform averages over lines, planes and points as sets. In (i), `a(P)` averages
over the lines `L ⊆ P`. In (ii), `Pr_{P, x ∈ P}` is `flatIncProb` (uniform plane, then uniform
point of it), `µ(B) = |B|/|P_{m,q}|`, `µ(X) = |X|/q^m`. In (iii), `G_x` is uniform on the ordered
pairs `(P, P′)` of planes through `x` with `P ∩ P′` a line, and `µ_x(B) = |B|/|P_x|`. -/
theorem lemma_4_1 :
    ∀ (F : Type u) [Field F] [Fintype F] (m : ℕ), 3 ≤ m →
      (∀ a : Line F m → ℝ, (∀ L, 0 ≤ a L ∧ a L ≤ 1) →
        (∑ P : Plane F m,
            ((∑ L ∈ Finset.univ.filter (fun L : Line F m => L.carrier ⊆ P.carrier), a L) /
                ((Finset.univ.filter (fun L : Line F m => L.carrier ⊆ P.carrier)).card : ℝ) -
              (∑ L : Line F m, a L) / (Fintype.card (Line F m) : ℝ)) ^ 2) /
            (Fintype.card (Plane F m) : ℝ) ≤ 4 / (Fintype.card F : ℝ)) ∧
      (∀ (B : Finset (Plane F m)) (X : Finset (Fin m → F)),
        |flatIncProb X B - flatMeasure B * ptMeasure X| ≤
          2 / (Fintype.card F : ℝ) * Real.sqrt (flatMeasure B * ptMeasure X)) ∧
      (∀ (x : Fin m → F) (B₁ B₂ : Finset (Plane F m)),
        (∀ P ∈ B₁, x ∈ P.carrier) → (∀ P ∈ B₂, x ∈ P.carrier) →
        |(((pvpEdges F m).filter fun PP =>
              x ∈ PP.1.carrier ∧ x ∈ PP.2.carrier ∧ PP.1 ∈ B₁ ∧ PP.2 ∈ B₂).card : ℝ) /
            (((pvpEdges F m).filter fun PP => x ∈ PP.1.carrier ∧ x ∈ PP.2.carrier).card : ℝ) -
          (B₁.card : ℝ) / ((Finset.univ.filter fun P : Plane F m => x ∈ P.carrier).card : ℝ) *
            ((B₂.card : ℝ) / ((Finset.univ.filter fun P : Plane F m => x ∈ P.carrier).card : ℝ))| ≤
          1 / (Fintype.card F : ℝ) *
            Real.sqrt ((B₁.card : ℝ) /
                ((Finset.univ.filter fun P : Plane F m => x ∈ P.carrier).card : ℝ) *
              ((B₂.card : ℝ) /
                ((Finset.univ.filter fun P : Plane F m => x ∈ P.carrier).card : ℝ)))) := by sorry

end LineVsPoint
