-- Prove2me | Theorems.Thm_LineVsPoint_theorem_4_2
-- name    : LineVsPoint.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:48.683798+00:00
-- url     : https://prove2.me/theorems/b7cbb709-5000-4f5f-8a68-5adf71e09437
-- title:
--   Theorem 4.2 — plane–versus–plane soundness (Bhangale–Richelson)
-- statement:
--   **Theorem 4.2** (Bhangale–Richelson, cited from [BR26]). There is an absolute constant $C_{\mathrm{BR}}>0$ such that the following holds for every finite field $\mathbb F_q$, every $m\ge3$ and $d\ge1$. If a degree-$d$ plane table $T$ satisfies
--
--   $$
--   \mathrm{Acc}_{\mathrm{PVP}}(T)\ge C_{\mathrm{BR}}\frac dq,
--   $$
--
--   then there is a global polynomial $Q\in\mathbb F_q[X_1,\dots,X_m]$ of total degree at most $d$ satisfying
--
--   $$
--   \Pr_{P\in\mathcal P_{m,q}}\bigl[T(P)=Q|_P\bigr]\ge\frac1{10}\,\mathrm{Acc}_{\mathrm{PVP}}(T).
--   $$
--
--   $\mathrm{Acc}_{\mathrm{PVP}}(T)$ is the probability that two planes meeting in a line, chosen uniformly, have plane polynomials agreeing on the line. The paper cites this theorem; it is the input that bootstraps the bivariate bound to every dimension.
--
--   Differences from the source:
--   - reading: the standing assumptions of §4.1 ('Through Section 4.1 let m ≥ 3', p.17) and the d ≥ 1 of Theorems 1.1 and 3.1 → hypotheses 3 ≤ m and 1 ≤ d; reason: the theorem is stated and used inside §4.1 with these d and m
--   - reading: T(P) = Q|_P → the formal identity Q(a_P + s u₁ + t u₂) = T(P) in F[s, t]; reason: the stronger reading; for d < q it is equality of functions on P, and for d ≥ q the hypothesis fails once C_BR > 1
--   - reading: T(P)|_{P∩P′} = T(P′)|_{P∩P′} → the two plane polynomials take the same value at every point of P ∩ P′; reason: the weaker event, so the hypothesis on Acc_PVP is weaker; for d < q it is the same as equality of the restricted polynomials
--   - encoding: a degree-d plane table with each plane's fixed parameterization → PlaneTable F m d, quantified over every parameterization; reason: the parameterization is arbitrary, as for lines
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Theorem 4.2, p.18

import Definitions.Def_LineVsPoint_accPVP

set_option autoImplicit false

universe u

namespace LineVsPoint

open Classical in
/-- **Theorem 4.2** (Bhangale–Richelson plane–versus–plane soundness, cited from [BR26]). *There
is an absolute constant `C_BR > 0` such that, if a degree-`d` plane table `T` satisfies
`Acc_PVP(T) ≥ C_BR d/q`, then there is a global polynomial `Q ∈ F_q[X_1, …, X_m]` of total degree
at most `d` satisfying `Pr_{P ∈ P_{m,q}}[T(P) = Q|_P] ≥ (1/10) Acc_PVP(T)`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Theorem 4.2, p.18.

**Formalization Note.** `m ≥ 3` is the standing assumption of §4.1 (p.17) and `d ≥ 1` that of
Theorems 1.1 and 3.1. `C_BR` is chosen before the field, `m`, `d` and `T`. The event
`T(P) = Q|_P` is the formal identity `Q(a + s u₁ + t u₂) = T(P)` in `F[s, t]`; the acceptance
event of `Acc_PVP` is agreement as functions on `P ∩ P′` (both coincide with the other readings
for `d < q`). -/
theorem theorem_4_2 :
    ∃ C_BR : ℝ, 0 < C_BR ∧
      ∀ (F : Type u) [Field F] [Fintype F] (m d : ℕ), 3 ≤ m → 1 ≤ d →
      ∀ T : PlaneTable F m d, C_BR * (d : ℝ) / (Fintype.card F : ℝ) ≤ accPVP T →
        ∃ Q : MvPolynomial (Fin m) F, Q.totalDegree ≤ d ∧
          1 / 10 * accPVP T ≤
            ((Finset.univ.filter fun P : Plane F m => planeRestrict T Q P = T.T P).card : ℝ) /
              (Fintype.card (Plane F m) : ℝ) := by sorry

end LineVsPoint
