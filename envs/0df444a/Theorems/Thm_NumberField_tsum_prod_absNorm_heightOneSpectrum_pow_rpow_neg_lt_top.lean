-- Prove2me | Theorems.Thm_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
-- name    : NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/32e6ce96-7acd-576e-ab14-4c00b53e84ac
-- title:
--   Finiteness of the Dedekind zeta series at real t>1
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and let $t$ be a real number with $1 < t$. Index the terms by finitely supported functions $k$ from the height-one spectrum of $\mathcal{O}_F$ (the nonzero prime ideals of $\mathcal{O}_F$) to $\mathbb{N}$. For such a $k$, form the natural number $\prod_{v} (\mathfrak{N} v)^{k_v}$, the product being taken over the support of $k$, where $\mathfrak{N} v =$ `Ideal.absNorm` of the prime ideal attached to $v$, i.e.\ the cardinality of $\mathcal{O}_F / v$; this is the absolute norm of the ideal $\prod_v v^{k_v}$. Cast this natural number into $\mathbb{R}_{\ge 0}^{\infty}$ and raise it to the real power $-t$ in the $\overline{\mathbb{R}}_{\ge 0}$-valued power operation. The assertion is that the unconditional $\mathbb{R}_{\ge 0}^{\infty}$-valued sum of these terms over all exponent vectors $k$ is strictly less than $\top$, that is, finite. Since every nonzero ideal of $\mathcal{O}_F$ arises from exactly one exponent vector, this is the convergence of the Dedekind zeta series $\sum_{\mathfrak{d}} (\mathfrak{N}\mathfrak{d})^{-t}$ of $F$ at real $t > 1$, in the form of finiteness of a sum in $\mathbb{R}_{\ge 0}^{\infty}$ rather than summability of a real series.
--
--   This is the classical convergence of the Dedekind zeta function of a number field on the real half-line $\operatorname{Re} s > 1$, packaged with the index set of finitely supported exponent vectors on the finite places, which is the index set produced by decomposing the finite adeles into boxes. It is used in the automorphic part of the argument to dominate products over the finite places, for instance in the estimates for Godement sections, unramified local integrands and the meromorphic continuation of Weyl intertwining integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.lean

import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
    (F : Type) [Field F] [NumberField F] {t : ℝ} (ht : 1 < t) :
    ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ,
        (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ℝ≥0∞) ^ (-t)) < ⊤ := by sorry
