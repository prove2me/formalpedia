-- Prove2me | Theorems.Thm_LatticePrepro_digitVal_gdigits
-- name    : LatticePrepro.digitVal_gdigits
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:15.516613+00:00
-- url     : https://prove2.me/theorems/4970aeec-3c8b-4d9c-b402-dcd6a1ae107f
-- title:
--   Claim A.2 (first part) — the generalized digits of $k$ have value $k$
-- statement:
--   Let $B\ge2$ and $m\ge1$ be integers. Then for every natural number $k$,
--   $$\mathrm{val}_B\bigl(\mathrm{digits}_{B,m}(k)\bigr)=\sum_{h=0}^{m-1}\mathrm{digits}_{B,m}(k)_h\,B^h=k .$$
--   Here $\mathrm{digits}_{B,m}(k)$ is the generalized digit vector of Definition A.1: writing $k=t\,(B^m-1)+b$ with $0\le b<B^m-1$, its $h$-th entry is $t\,(B-1)+b_h$, where $b_h$ is the $h$-th base-$B$ digit of $b$.
--
--   This makes the moment map $\hat\mu_k$ of Construction A.4, which is defined through the interpolant indexed by $\mathrm{digits}_{B,m}(k)$, a moment of order exactly $k$. Together with the additivity of $\mathrm{val}_B$, it identifies the polynomial matrix of an evaluation table at $\gamma$ with the Hankel matrix $(\hat\mu_{h+h'})$ (Lemma A.6), and it gives $\hat\mu_k=\alpha^k$ on the element tables (Theorem A.8).
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Claim A.2 (\label{clm:generalized-digits}), first part; Lean: LatticePrepro/Tables/Digits.lean, LatticePrepro.digitVal_gdigits

import Mathlib
import Definitions.Def_LatticePrepro_Tables_Digits

open LatticePrepro

theorem LatticePrepro.digitVal_gdigits {B m : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (k : ℕ) :
    digitVal B (gdigits B m k) = k := by sorry
