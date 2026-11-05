-- Prove2me | Theorems.Thm_JencovaRenyi_duality
-- name    : JencovaRenyi.duality
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:44:16.956871+00:00
-- url     : https://prove2.me/theorems/f6b14f7b-a8ef-4953-9e9c-5b95d15daf10
-- title:
--   Density of $L_\infty(\mathcal M,\varphi)$ and the duality $L_q(\mathcal M,\varphi)\simeq L_p(\mathcal M,\varphi)^*$
-- statement:
--   Let $\varphi$ be a normal state, $1\le p\le\infty$ and $1/p+1/q=1$.
--
--   1. **Density.** $\{h_x : x\in\mathcal M\}$ is dense in $L_r(\mathcal M,\varphi)$ for every $1\le r<\infty$.
--   2. **Extension.** For $h\in L_q(\mathcal M,\varphi)$ and $k\in L_p(\mathcal M,\varphi)$ the limit $\langle h,k\rangle = \lim_{h_x\to h} k(x)$ exists (along a proper filter) and $|\langle h,k\rangle|\le\|h\|_{q,\varphi}\|k\|_{p,\varphi}$.
--   3. **Consistency.** $\langle h_x,k\rangle = k(x) = \operatorname{Tr} kx$ for $x\in\mathcal M$.
--   4. **Isometry.** For $p<\infty$, $\|h\|_{q,\varphi} = \sup\{|\langle h,k\rangle| : \|k\|_{p,\varphi}\le1\}$ for $h\in L_q(\mathcal M,\varphi)$.
--   5. **Surjectivity.** For $p<\infty$, every bounded linear functional $L$ on $L_p(\mathcal M,\varphi)$ is $L = \langle h,\cdot\rangle$ for exactly one $h\in L_q(\mathcal M,\varphi)$.
--   6. **Symmetry.** $\langle h,k\rangle$ computed in $L_q\times L_p$ equals $\langle k,h\rangle$ computed in $L_p\times L_q$.
--
--   Together, 4 and 5 say that $L_q(\mathcal M,\varphi)$ is isometrically isomorphic to the Banach dual of $L_p(\mathcal M,\varphi)$, the duality used throughout §3.3.
--
--   Differences from the source:
--   - encoding: a von Neumann algebra $\mathcal M$ in standard form $(\lambda(\mathcal M), L_2(\mathcal M), J, L_2(\mathcal M)^+)$ (p.3) → a unital star subalgebra `A` of $B(H)$ with a `StandardForm A` (reference `Claimed50.P06`: bicommutant property, conjugation $J$, self-dual cone, $J\mathcal MJ = \mathcal M'$, cone invariance, central compatibility); reason: every von Neumann algebra has a standard form, unique up to unitary equivalence, so no instance is lost.
--   - encoding: Haagerup's $L_1(\mathcal M)$ with $h_\psi \leftrightarrow \psi$ and $\operatorname{Tr} h_\psi = \psi(1)$ (p.3); $\mathcal M_*^+$ its positive part → `Predual A`, the norm closure of the span of the vector functionals $a \mapsto \langle \xi, a\eta\rangle$ in the dual of `A`, with the dual norm; positivity is $\psi(a^*a) \ge 0$; reason: p.3 identifies $\mathcal M_*$ with $L_1(\mathcal M)$ isometrically; the normal functionals are exactly that closed span.
--   - generalization: $\mathcal M$ (and $\mathcal N$) $\sigma$-finite (p.3) → no $\sigma$-finiteness assumption; reason: every object lives on $e\mathcal Me$, $e = s(\varphi)$, which carries the faithful normal state $\varphi|_{e\mathcal Me}$ and so is $\sigma$-finite whatever $\mathcal M$ is; the statement specializes to $\sigma$-finite algebras.
--   - generalization: $\varphi$ a faithful normal state (§2, p.4) → every normal state $\varphi$, with $L_p(\mathcal M,\varphi)$ as extended to non-faithful states in §3, p.10; reason: for faithful $\varphi$ the support clause is automatic and $x \mapsto h_x$ is injective, so the statement specializes to the paper's.
--   - encoding: $L_p(\mathcal M,\varphi) := C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$ with norm $\|\cdot\|_{p,\varphi}$ (p.5), on $e\mathcal Me$ for non-faithful $\varphi$ (p.10) → the extended gauge `lpNorm S φ p` on the predual with values in $[0,\infty]$, $\infty$ off the space; membership is `lpNorm S φ p k < ⊤`; for non-faithful $\varphi$ it interpolates $\{h_x\}$ against all of $L_1(\mathcal M)$, with the support clause $k = eke$ at $p = 1$; reason: the same spaces and norms: for an admissible $f$, $f - efe$ is bounded, analytic in the strip and zero on $\operatorname{Re} z = 0$, hence zero.
--   - encoding: the duality "given by" (7), $\langle h_\varphi^{1/2q}k_1h_\varphi^{1/2q}, h_\varphi^{1/2p}k_2h_\varphi^{1/2p}\rangle = \operatorname{Tr}k_1k_2$ through Haagerup's $L_p(\mathcal M)$ → the extension of $\langle h_x,k\rangle = k(x)$ by continuity (`pairing`), with clauses 2 and 3; reason: (7) is continuous and agrees with $\operatorname{Tr}kx$ on the dense set $\{h_x\}$, so it is the same pairing; the formula itself is about Haagerup's $L_p(\mathcal M)$, which is absent, and this item does not state it (like Theorem 2.3, it is outside the mission).
--   - encoding: "$L_q(\mathcal M,\varphi)$ is isometrically isomorphic to the Banach space dual of $L_p(\mathcal M,\varphi)$" → clauses 4 and 5, with bounded functionals given as linear maps on $L_1(\mathcal M)$ bounded on $L_p(\mathcal M,\varphi)$; reason: $L_p(\mathcal M,\varphi)$ is not a Lean type; every functional on it extends linearly to $L_1(\mathcal M)$.
--   - generalization: density in $L_1(\mathcal M)$ and in $L_p(\mathcal M,\varphi)$, $p>1$; the pairing written on either side → also clause 6 (symmetry of the pairing); reason: an added true conclusion the paper uses when it pairs $h\in L_\beta$ with $h_\psi\in L_\alpha$ from either side (p.17); dropping it gives the paper's statement.
--   - encoding: the reiteration identity (6), which the milestone's quoted passage runs through → not stated by this item; reason: (6) is a separate statement between the density sentence and the duality, used neither here nor by the goal; the item's claim is density, the extension of the duality and the isometric identification.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2.2, p.6 (density, the duality extending $\langle k,h_x\rangle := \operatorname{Tr} kx$, and the isometric identification of the dual)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_symmEmbed
import Definitions.Def_JencovaRenyi_lpNorm
import Definitions.Def_JencovaRenyi_pairing
open scoped ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

/-- The duality of `L_p(M, φ)` and `L_q(M, φ)`, Jenčová, arXiv:1609.08462v4, §2.2, p.6. Let
`1 ≤ p ≤ ∞`, `1/p + 1/q = 1`, `φ` a normal state.

1. `L_∞(M, φ) = {h_x}` is dense in `L_r(M, φ)` for every `1 ≤ r < ∞` ("dense in `L_1(M)` and
   therefore also in `L_p(M, φ)`").
2. The duality `⟨h_x, k⟩ := Tr k x = k(x)` extends to `h ∈ L_q(M, φ)`, `k ∈ L_p(M, φ)`: the limit
   defining `⟨h, k⟩` exists along a proper filter, and `|⟨h, k⟩| ≤ ‖h‖_{q,φ} ‖k‖_{p,φ}`.
3. `⟨h_x, k⟩ = k(x)` for `x ∈ M`.
4. For `p < ∞`, `‖h‖_{q,φ} = sup {|⟨h, k⟩| : ‖k‖_{p,φ} ≤ 1}` (the identification is isometric).
5. For `p < ∞`, every bounded linear functional on `L_p(M, φ)` is `⟨h, ·⟩` for exactly one
   `h ∈ L_q(M, φ)` ("`L_q(M, φ)` is isometrically isomorphic to the Banach space dual of
   `L_p(M, φ)`").
6. The pairing is symmetric: `⟨h, k⟩` computed in `L_q × L_p` equals `⟨k, h⟩` computed in
   `L_p × L_q`. -/
theorem duality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (S : StandardForm A) (φ : Predual A) (hφ : IsNormalState A (φ : A →L[ℂ] ℂ))
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p⁻¹ + q⁻¹ = 1) :
    (∀ r : ℝ≥0∞, 1 ≤ r → r ≠ ⊤ → ∀ h : Predual A, lpNorm S φ r h < ⊤ →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ x : A, lpNorm S φ r (h - symmEmbed S φ x) < ε) ∧
    (∀ h k : Predual A, lpNorm S φ q h < ⊤ → lpNorm S φ p k < ⊤ →
      (Filter.comap (fun x : A => lpNorm S φ q (h - symmEmbed S φ x)) (nhds 0)).NeBot ∧
      Filter.Tendsto (fun x : A => (k : A →L[ℂ] ℂ) x)
        (Filter.comap (fun x : A => lpNorm S φ q (h - symmEmbed S φ x)) (nhds 0))
        (nhds (pairing S φ q h k)) ∧
      (‖pairing S φ q h k‖₊ : ℝ≥0∞) ≤ lpNorm S φ q h * lpNorm S φ p k) ∧
    (∀ (x : A) (k : Predual A), lpNorm S φ p k < ⊤ →
      pairing S φ q (symmEmbed S φ x) k = (k : A →L[ℂ] ℂ) x) ∧
    (p ≠ ⊤ → ∀ h : Predual A, lpNorm S φ q h < ⊤ →
      lpNorm S φ q h = ⨆ (k : Predual A) (_ : lpNorm S φ p k ≤ 1),
        (‖pairing S φ q h k‖₊ : ℝ≥0∞)) ∧
    (p ≠ ⊤ → ∀ (L : Predual A →ₗ[ℂ] ℂ) (C : ℝ),
      (∀ k : Predual A, lpNorm S φ p k < ⊤ → ‖L k‖ ≤ C * (lpNorm S φ p k).toReal) →
      ∃! h : Predual A, lpNorm S φ q h < ⊤ ∧
        ∀ k : Predual A, lpNorm S φ p k < ⊤ → L k = pairing S φ q h k) ∧
    (∀ h k : Predual A, lpNorm S φ q h < ⊤ → lpNorm S φ p k < ⊤ →
      pairing S φ q h k = pairing S φ p k h) := by sorry

end JencovaRenyi
