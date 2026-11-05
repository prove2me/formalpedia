-- Prove2me | Theorems.Thm_JencovaRenyi_theorem_2_5
-- name    : JencovaRenyi.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:42.821431+00:00
-- url     : https://prove2.me/theorems/e4943413-a952-4e69-babf-830e9c398b0f
-- title:
--   Theorem 2.5 — Clarkson inequalities in $L_p(\mathcal M,\varphi)$
-- statement:
--   Let $\varphi$ be a normal state, $h,k\in L_p(\mathcal M,\varphi)$, $1\le p\le\infty$, $1/p+1/q=1$, and write $\|\cdot\| = \|\cdot\|_{p,\varphi}$.
--
--   1. For $2\le p<\infty$:
--   $$
--   \Big[\tfrac12\big(\|h+k\|^p+\|h-k\|^p\big)\Big]^{1/p}\le\big(\|h\|^q+\|k\|^q\big)^{1/q}.
--   $$
--   2. For $p=\infty$ ($q = 1$): $\max(\|h+k\|,\|h-k\|)\le\|h\|+\|k\|$.
--   3. For $1<p\le2$ the inequality of 1 reverses.
--   4. For $p = 1$ ($q=\infty$): $\max(\|h\|,\|k\|)\le\tfrac12(\|h+k\|+\|h-k\|)$.
--
--   They imply that $L_p(\mathcal M,\varphi)$ is uniformly convex and uniformly smooth for $1<p<\infty$; the case $p = \beta\le2$ gives the first lower bound of Theorem 3.14.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - generalization: $\varphi$ a faithful normal state (§2, p.4) → every normal state $\varphi$, with $L_p(\mathcal M,\varphi)$ as extended to non-faithful states in §3, p.10; reason: for faithful $\varphi$ the support clause is automatic and $x \mapsto h_x$ is injective, so the statement specializes to the paper's.
--   - encoding: $L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$ with norm $\|\cdot\|_{p,\varphi}$ (p.5), on $e\mathcal Me$ for non-faithful $\varphi$ (p.10) → the extended gauge `lpNorm S φ p` on the predual with values in $[0,\infty]$, $\infty$ off the space; membership is `lpNorm S φ p k < ⊤`; for non-faithful $\varphi$ it interpolates $\{h_x\}$ against all of $L_1(\mathcal M)$, with the support clause $k = eke$ at $p = 1$; reason: the same spaces and norms: for an admissible $f$, $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re} z = 0$, hence zero.
--   - reading: $[\frac12(\cdot^p+\cdot^p)]^{1/p}$ at $p=\infty$ and $(\cdot^q+\cdot^q)^{1/q}$ at $q=\infty$ → $\max$ of the two norms (clauses 2 and 4); reason: the only meaning of these power means at an infinite exponent, their limit.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, Theorem 2.5, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_lpNorm
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Theorem 2.5 of Jenčová, arXiv:1609.08462v4, p.6 (Clarkson inequalities). Let
`h, k ∈ L_p(M, φ)`, `1 ≤ p ≤ ∞`, `1/p + 1/q = 1`. For `2 ≤ p ≤ ∞`,
`[½(‖h + k‖^p_{p,φ} + ‖h − k‖^p_{p,φ})]^{1/p} ≤ (‖h‖^q_{p,φ} + ‖k‖^q_{p,φ})^{1/q}`;
for `1 ≤ p ≤ 2` the inequality reverses. At `p = ∞` (`q = 1`) the left side is
`max(‖h + k‖, ‖h − k‖)`; at `p = 1` (`q = ∞`) the right side is `max(‖h‖, ‖k‖)`. -/
theorem theorem_2_5 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (S : StandardForm A) (φ : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ))
    (h k : Predual A) :
    (∀ p q : ℝ, 2 ≤ p → 1 / p + 1 / q = 1 →
      lpNorm S φ (ENNReal.ofReal p) h < ⊤ → lpNorm S φ (ENNReal.ofReal p) k < ⊤ →
      ((1 / 2) * ((lpNorm S φ (ENNReal.ofReal p) (h + k)).toReal ^ p + (lpNorm S φ (ENNReal.ofReal p) (h - k)).toReal ^ p)) ^ (1 / p) ≤
        ((lpNorm S φ (ENNReal.ofReal p) h).toReal ^ q + (lpNorm S φ (ENNReal.ofReal p) k).toReal ^ q) ^ (1 / q)) ∧
    (lpNorm S φ ⊤ h < ⊤ → lpNorm S φ ⊤ k < ⊤ →
      max (lpNorm S φ ⊤ (h + k)).toReal (lpNorm S φ ⊤ (h - k)).toReal ≤
        (lpNorm S φ ⊤ h).toReal + (lpNorm S φ ⊤ k).toReal) ∧
    (∀ p q : ℝ, 1 < p → p ≤ 2 → 1 / p + 1 / q = 1 →
      lpNorm S φ (ENNReal.ofReal p) h < ⊤ → lpNorm S φ (ENNReal.ofReal p) k < ⊤ →
      ((lpNorm S φ (ENNReal.ofReal p) h).toReal ^ q + (lpNorm S φ (ENNReal.ofReal p) k).toReal ^ q) ^ (1 / q) ≤
        ((1 / 2) * ((lpNorm S φ (ENNReal.ofReal p) (h + k)).toReal ^ p + (lpNorm S φ (ENNReal.ofReal p) (h - k)).toReal ^ p)) ^ (1 / p)) ∧
    (lpNorm S φ 1 h < ⊤ → lpNorm S φ 1 k < ⊤ →
      max (lpNorm S φ 1 h).toReal (lpNorm S φ 1 k).toReal ≤
        (1 / 2) * ((lpNorm S φ 1 (h + k)).toReal + (lpNorm S φ 1 (h - k)).toReal)) := by sorry

end JencovaRenyi
