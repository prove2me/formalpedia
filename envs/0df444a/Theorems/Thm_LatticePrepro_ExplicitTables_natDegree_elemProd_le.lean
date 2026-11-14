-- Prove2me | Theorems.Thm_LatticePrepro_ExplicitTables_natDegree_elemProd_le
-- name    : LatticePrepro.ExplicitTables.natDegree_elemProd_le
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:47.4102+00:00
-- url     : https://prove2.me/theorems/d71a9700-bd0b-4dca-b8a3-0662fb5c0618
-- title:
--   Degree bound for products of element polynomials
-- statement:
--   Let $p$ be a prime and fix a field setup with sample field $\mathbb{S}$ and extension $K=\mathbb{S}(\gamma)$ of degree $\delta$ (every element of $K$ is $f(\gamma)$ with $f\in\mathbb{S}[X]$, $\deg f<\delta$). Let $m,B$ be natural numbers, $\alpha\in K$, and let $\ell_0,\dots,\ell_{m-1}\in\mathbb{S}[X]$ be the element polynomials of $\alpha$, so that $\deg\ell_h<\delta$ and $\ell_h(\gamma)=\alpha^{B^h}$. If $\eta\in\mathbb{N}^m$ satisfies $\eta_h\le2p(B-1)$ for every $h$, i.e. $\eta$ lies in the index set $\{0,\dots,2p(B-1)\}^m$, then
--   $$\deg\prod_{h=0}^{m-1}\ell_h^{\eta_h}\le\Delta=2pm(B-1)(\delta-1).$$
--
--   This is the estimate $\deg\prod_h\ell_h^{\eta_h}\le(\delta-1)\sum_h\eta_h\le\Delta$ in the completeness part of the proof of Theorem A.8. Since the interpolants of the element table $\hat e_\alpha$ are exactly these products, it shows that element tables satisfy the low-degree constraints of Construction A.4.
--
--   **Formalization Note**: The degree is Mathlib's `natDegree` (the zero polynomial has degree $0$). No hypotheses on $m$, $B$ or $\delta$ are needed.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847); auxiliary lemma used in the proof of Theorem A.8 (\label{thm:moment-representation-construction}); Lean: LatticePrepro/Tables/ElementTable.lean, LatticePrepro.ExplicitTables.natDegree_elemProd_le

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable

open LatticePrepro
open Polynomial
open LatticePrepro.ExplicitTables
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)
variable {FS m B}

theorem LatticePrepro.ExplicitTables.natDegree_elemProd_le (α : FS.K) {η : Fin m → ℕ} (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    (elemProd FS m B α η).natDegree ≤ degBound p m B δ := by sorry
