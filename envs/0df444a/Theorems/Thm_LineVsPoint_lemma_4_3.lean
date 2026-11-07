-- Prove2me | Theorems.Thm_LineVsPoint_lemma_4_3
-- name    : LineVsPoint.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:04:56.954459+00:00
-- url     : https://prove2.me/theorems/e1ea4062-400d-435c-acdf-ce1811353bfb
-- title:
--   Lemma 4.3 — plane–versus–point decoding
-- statement:
--   **Lemma 4.3.** There are absolute constants $C_{\mathrm{PP}},c_{\mathrm{PP}}>0$ such that the following holds for every finite field $\mathbb F_q$, every $m\ge3$, $d\ge1$, every point table $f:\mathbb F_q^m\to\mathbb F_q$ and every agreement threshold $\beta\ge C_{\mathrm{PP}}\sqrt{d/q}$. Let $\mathcal G\subseteq\mathcal P_{m,q}$ have measure at least $1/2$, and suppose that for every $P\in\mathcal G$ we are given a degree-$d$ polynomial $T(P)$ on $P$ with
--
--   $$
--   \Pr_{x\in P}\bigl[T(P)(x)=f(x)\bigr]\ge\beta .
--   $$
--
--   Then there exists a global polynomial $Q$ of total degree at most $d$ such that
--
--   $$
--   \Pr_{x\in\mathbb F_q^m}\bigl[Q(x)=f(x)\bigr]\ge c_{\mathrm{PP}}\,\beta .
--   $$
--
--   This is the form in which Theorem 4.2 enters the proof of Theorem 3.1 for $m\ge3$.
--
--   Differences from the source:
--   - reading: the standing assumptions of §4.1 (m ≥ 3, p.17) and d ≥ 1 (Theorems 1.1, 3.1; the proof uses 'because d ≥ 1') → hypotheses 3 ≤ m and 1 ≤ d; reason: the lemma is stated and proved inside §4.1 under these assumptions
--   - encoding: a degree-d polynomial T(P) for every P ∈ G → a degree-d plane table T, constrained only on G; reason: every family on G extends to a total table
--   - encoding: G ⊆ P_{m,q} of measure at least 1/2 → a finite set G of planes with |G| / #planes ≥ 1/2; reason: the measure is the uniform density among planes
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 4.3, p.18

import Definitions.Def_LineVsPoint_PlaneTable
import Definitions.Def_LineVsPoint_agr

set_option autoImplicit false

universe u

namespace LineVsPoint

/-- **Lemma 4.3** (plane–versus–point decoding). *There are absolute constants
`C_PP, c_PP > 0` such that the following holds for every agreement threshold
`β ≥ C_PP √(d/q)`. Let `G ⊆ P_{m,q}` have measure at least `1/2`, and suppose that for every
`P ∈ G` we are given a degree-`d` polynomial `T(P)` satisfying `Pr_{x∈P}[T(P)(x) = f(x)] ≥ β`.
Then there exists a global degree-`d` polynomial `Q` such that
`Pr_{x∈F^m_q}[Q(x) = f(x)] ≥ c_PP β`.* Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is
Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…), Lemma 4.3, p.18.

**Formalization Note.** `m ≥ 3` (§4.1, p.17) and `d ≥ 1` (Theorems 1.1, 3.1) are standing
assumptions. `C_PP, c_PP` are chosen before the field, `m`, `d`, `f`, `β`, `G` and the plane
polynomials. The polynomials `T(P)` (with the planes' parameterizations) are those of a degree-`d`
plane table, constrained only on `G`. A global degree-`d` polynomial is a `Q ∈ F[X₁, …, X_m]` of
total degree `≤ d`, and `Pr_x[Q(x) = f(x)]` is `agr f Q`. -/
theorem lemma_4_3 :
    ∃ C_PP c_PP : ℝ, 0 < C_PP ∧ 0 < c_PP ∧
      ∀ (F : Type u) [Field F] [Fintype F] (m d : ℕ), 3 ≤ m → 1 ≤ d →
      ∀ (f : (Fin m → F) → F) (β : ℝ),
        C_PP * Real.sqrt ((d : ℝ) / (Fintype.card F : ℝ)) ≤ β →
      ∀ (G : Finset (Plane F m)), 1 / 2 ≤ (G.card : ℝ) / (Fintype.card (Plane F m) : ℝ) →
      ∀ T : PlaneTable F m d, (∀ P ∈ G, β ≤ planeAgr f T P) →
        ∃ Q : MvPolynomial (Fin m) F, Q.totalDegree ≤ d ∧ c_PP * β ≤ agr f Q := by sorry

end LineVsPoint
