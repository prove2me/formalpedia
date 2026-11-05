-- Prove2me | Theorems.Thm_JencovaRenyi_lemma_2_1
-- name    : JencovaRenyi.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:48.72991+00:00
-- url     : https://prove2.me/theorems/ec720f0e-8b38-44be-9992-cb05c699ba08
-- title:
--   Lemma 2.1 — $k = h_x$ with $x \ge 0$ iff $k\le\lambda h_\varphi$, and $\|k\|_{\infty,\varphi} = \inf\{\lambda>0 : k\le\lambda h_\varphi\}$
-- statement:
--   Let $\varphi$ be a normal state on $\mathcal M$ and $k\in L_1(\mathcal M)^+$. Then
--
--   1. $k = h_x$ for some positive $x\in\mathcal M$ if and only if $k\le\lambda h_\varphi$ for some $\lambda>0$;
--   2. in this case
--   $$
--   \|k\|_{\infty,\varphi} = \inf\{\lambda>0 : k\le\lambda h_\varphi\};
--   $$
--   3. if moreover $\varphi$ is faithful and $k = h_x$ with $x\ge0$, then $\|k\|_{\infty,\varphi} = \|x\|$.
--
--   The lemma identifies the positive part of $L_\infty(\mathcal M,\varphi)$ with the functionals dominated by a multiple of $\varphi$; §3.3 uses it to show that a positive map sends $L_\infty(\mathcal M,\varphi)$ into $L_\infty(\mathcal N,\Phi(\varphi))$.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - generalization: $\varphi$ a faithful normal state (§2.1, p.4) → clauses 1 and 2 for every normal state $\varphi$; clause 3 ($\|k\|_{\infty,\varphi} = \|x\|$) for faithful $\varphi$, as in the paper; reason: for faithful $\varphi$ the statement is the paper's; for non-faithful $\varphi$ the representing $x$ is not unique, so clause 3 is kept faithful-only.
--   - encoding: $\|\cdot\|_{\infty,\varphi}$ defined on $L_\infty(\mathcal M,\varphi)$ → `infNorm`, the infimum of $\|x\|$ over $h_x = k$, $\infty$ off the space; reason: equals $\|x\|$ for faithful $\varphi$ (p.4) and $\|exe\|$ in general (p.10).
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, Lemma 2.1, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_symmEmbed
import Definitions.Def_JencovaRenyi_infNorm
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- Lemma 2.1 of Jenčová, arXiv:1609.08462v4, p.4. Let `k ∈ L_1(M)^+`. Then `k = h_x` for some
`x ∈ M^+` if and only if `k ≤ λ h_φ` for some `λ > 0`. In this case
`‖k‖_{∞,φ} = inf {λ > 0, k ≤ λ h_φ}`, and, for `φ` faithful, `‖k‖_{∞,φ} = ‖x‖`.

Stated for every normal state `φ` (the paper fixes `φ` faithful in §2 and passes to `eMe` in §3);
the clause `‖k‖_{∞,φ} = ‖x‖` is stated for faithful `φ`, as in the paper. -/
theorem lemma_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (S : StandardForm A) (φ k : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ))
    (hk : IsPositive k) :
    ((∃ x : A, 0 ≤ (x : H →L[ℂ] H) ∧ symmEmbed S φ x = k) ↔
      ∃ c : ℝ, 0 < c ∧ PredualLE k ((c : ℂ) • φ)) ∧
    ((∃ c : ℝ, 0 < c ∧ PredualLE k ((c : ℂ) • φ)) →
      infNorm S φ k = ⨅ (c : ℝ) (_ : 0 < c) (_ : PredualLE k ((c : ℂ) • φ)), ENNReal.ofReal c) ∧
    (IsFaithful A (φ : A →L[ℂ] ℂ) → ∀ x : A, 0 ≤ (x : H →L[ℂ] H) → symmEmbed S φ x = k →
      infNorm S φ k = (‖x‖₊ : ℝ≥0∞)) := by sorry

end JencovaRenyi
