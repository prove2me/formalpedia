-- Prove2me | Theorems.Thm_JencovaRenyi_theorem_2_6
-- name    : JencovaRenyi.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:38.998548+00:00
-- url     : https://prove2.me/theorems/041d4f0f-d942-4f7b-bbc6-9e211343565c
-- title:
--   Theorem 2.6 — $(\|h\|_p^2+(p-1)\|k\|_p^2)^{1/2}\le[\frac12(\|h+k\|_p^p+\|h-k\|_p^p)]^{1/p}$, $1<p\le2$
-- statement:
--   Let $\varphi$ be a normal state, $h,k\in L_p(\mathcal M,\varphi)$ and $\|\cdot\|_p = \|\cdot\|_{p,\varphi}$. For $1<p\le2$,
--   $$
--   \big(\|h\|_p^2+(p-1)\|k\|_p^2\big)^{1/2}\le\Big[\tfrac12\big(\|h+k\|_p^p+\|h-k\|_p^p\big)\Big]^{1/p},
--   $$
--   and for $2<p<\infty$ the inequality reverses.
--
--   This is the 2-uniform convexity (resp. smoothness) of $L_p(\mathcal M,\varphi)$ with the optimal constant $p-1$; it gives the second lower bound of Theorem 3.14, for $\beta\le 2$.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - generalization: $\varphi$ a faithful normal state (§2, p.4) → every normal state $\varphi$, with $L_p(\mathcal M,\varphi)$ as extended to non-faithful states in §3, p.10; reason: for faithful $\varphi$ the support clause is automatic and $x \mapsto h_x$ is injective, so the statement specializes to the paper's.
--   - encoding: $L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$ with norm $\|\cdot\|_{p,\varphi}$ (p.5), on $e\mathcal Me$ for non-faithful $\varphi$ (p.10) → the extended gauge `lpNorm S φ p` on the predual with values in $[0,\infty]$, $\infty$ off the space; membership is `lpNorm S φ p k < ⊤`; for non-faithful $\varphi$ it interpolates $\{h_x\}$ against all of $L_1(\mathcal M)$, with the support clause $k = eke$ at $p = 1$; reason: the same spaces and norms: for an admissible $f$, $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re} z = 0$, hence zero.
--   - reading: $\|\cdot\|_p$ → $\|\cdot\|_{p,\varphi}$; reason: the theorem is about $L_p(\mathcal M,\varphi)$; the subscript $\varphi$ is dropped on the page.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, Theorem 2.6, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_lpNorm
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Theorem 2.6 of Jenčová, arXiv:1609.08462v4, p.6 (2-uniform convexity and smoothness). Let
`h, k ∈ L_p(M, φ)`, `1 < p ≤ 2`. Then
`(‖h‖²_{p,φ} + (p − 1)‖k‖²_{p,φ})^{1/2} ≤ [½(‖h + k‖^p_{p,φ} + ‖h − k‖^p_{p,φ})]^{1/p}`.
For `2 < p < ∞` the inequality reverses. -/
theorem theorem_2_6 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (S : StandardForm A) (φ : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ))
    (h k : Predual A) (p : ℝ) (hp : 1 < p)
    (hh : lpNorm S φ (ENNReal.ofReal p) h < ⊤) (hk : lpNorm S φ (ENNReal.ofReal p) k < ⊤) :
    (p ≤ 2 →
      ((lpNorm S φ (ENNReal.ofReal p) h).toReal ^ 2 + (p - 1) * (lpNorm S φ (ENNReal.ofReal p) k).toReal ^ 2) ^ ((1 : ℝ) / 2) ≤
        ((1 / 2) * ((lpNorm S φ (ENNReal.ofReal p) (h + k)).toReal ^ p + (lpNorm S φ (ENNReal.ofReal p) (h - k)).toReal ^ p)) ^ (1 / p)) ∧
    (2 < p →
      ((1 / 2) * ((lpNorm S φ (ENNReal.ofReal p) (h + k)).toReal ^ p + (lpNorm S φ (ENNReal.ofReal p) (h - k)).toReal ^ p)) ^ (1 / p) ≤
        ((lpNorm S φ (ENNReal.ofReal p) h).toReal ^ 2 + (p - 1) * (lpNorm S φ (ENNReal.ofReal p) k).toReal ^ 2) ^ ((1 : ℝ) / 2)) := by sorry

end JencovaRenyi
