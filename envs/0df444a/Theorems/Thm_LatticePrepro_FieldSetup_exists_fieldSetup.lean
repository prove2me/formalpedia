-- Prove2me | Theorems.Thm_LatticePrepro_FieldSetup_exists_fieldSetup
-- name    : LatticePrepro.FieldSetup.exists_fieldSetup
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:10.233644+00:00
-- url     : https://prove2.me/theorems/4b9f2758-2fce-43ee-a3ef-5470237fcf8a
-- title:
--   Lemma A.3 (existence part) — field setups exist
-- statement:
--   Let $p$ be a prime and let $d,\delta$ be integers with $d\ge1$ and $\delta\ge1$. Then there exists a field setup with parameters $p,d,\delta$: a finite field $\mathbb{S}$ with $|\mathbb{S}|=p^d$, a field $K$ that is an algebra over $\mathbb{F}_p$ and over $\mathbb{S}$ (compatibly), and an element $\gamma\in K$ such that
--   $$K=\{f(\gamma): f\in\mathbb{S}[X],\ \deg f<\delta\}$$
--   and $1,\gamma,\dots,\gamma^{\delta-1}$ are linearly independent over $\mathbb{S}$. In other words, $K=\mathbb{S}(\gamma)$ is an extension of $\mathbb{S}$ of degree $\delta$ with power basis $1,\gamma,\dots,\gamma^{\delta-1}$.
--
--   This provides the fields of step 1 of Construction A.4. In Theorem A.8 it is applied with $\delta$ the least power of $p$ that is at least $S$, and $p^d$ the least power of $p$ that is at least $8pmB\delta$.
--
--   **Formalization Note**: The conclusion is `Nonempty (FieldSetup p d δ)`. Only existence is formalized: the paper's Lemma A.3 also constructs an irreducible $f$ with $\mathbb{S}=\mathbb{F}_p[X]/(f)$ and builds $K$ as an Artin–Schreier tower (for $\delta$ a power of $p$) in polynomial time, which is not part of this statement. Here $\delta$ may be any positive integer.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma A.3 (\label{lem:explicit-fields}), existence part; Lean: LatticePrepro/Tables/FieldSetup.lean, LatticePrepro.FieldSetup.exists_fieldSetup

import Mathlib
import Definitions.Def_LatticePrepro_Tables_FieldSetup

open LatticePrepro
open LatticePrepro.FieldSetup
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ}

theorem LatticePrepro.FieldSetup.exists_fieldSetup (p : ℕ) [Fact p.Prime] (d δ : ℕ) (hd : 1 ≤ d) (hδ : 1 ≤ δ) :
    Nonempty (FieldSetup p d δ) := by sorry
