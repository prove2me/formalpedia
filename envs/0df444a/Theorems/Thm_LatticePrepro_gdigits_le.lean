-- Prove2me | Theorems.Thm_LatticePrepro_gdigits_le
-- name    : LatticePrepro.gdigits_le
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:23.464514+00:00
-- url     : https://prove2.me/theorems/f69171fc-a6d3-4156-9e36-ed790b70ce57
-- title:
--   Claim A.2 (second part) — bound on the generalized digits
-- statement:
--   Let $B\ge2$, $m\ge1$ and $J\ge1$ be integers, and let $k$ be a natural number with
--   $$k\le J\cdot(B^m-1).$$
--   Then every entry of the generalized digit vector of $k$ (Definition A.1) is at most $J\cdot(B-1)$: for every $h\in\{0,\dots,m-1\}$,
--   $$\mathrm{digits}_{B,m}(k)_h\le J\cdot(B-1),$$
--   that is, $\mathrm{digits}_{B,m}(k)\in\{0,\dots,J(B-1)\}^m$.
--
--   In Appendix A this is used with $J=p$ and $J=2p$. It shows that the vectors $\mathrm{digits}(h)+\mathrm{digits}(h')$ with $h,h'<\ell=p(B^m-1)+1$ (Definition A.5) and the vectors $\mathrm{digits}(k)$ with $k\le2p(B^m-1)$ (Theorem A.8) lie in the index set $\{0,\dots,2p(B-1)\}^m$ on which the constraints of Construction A.4 are imposed.
--
--   **Formalization Note**: The paper's lower bound $0$ is automatic, since the entries are natural numbers.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Claim A.2 (\label{clm:generalized-digits}), second part; Lean: LatticePrepro/Tables/Digits.lean, LatticePrepro.gdigits_le

import Mathlib
import Definitions.Def_LatticePrepro_Tables_Digits

open LatticePrepro

theorem LatticePrepro.gdigits_le {B m J k : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (hJ : 1 ≤ J)
    (hk : k ≤ J * (B ^ m - 1)) (h : Fin m) : gdigits B m k h ≤ J * (B - 1) := by sorry
