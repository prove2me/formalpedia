-- Prove2me | Theorems.Thm_LIPAlgorithm_theorem_5_12
-- name    : LIPAlgorithm.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:22.041193+00:00
-- url     : https://prove2.me/theorems/93947846-3b13-47a0-ae90-9926a59de116
-- title:
--   Theorem 5.12 — Haviv–Regev-derived lattice canonicalizer
-- statement:
--   There are functions $\mathrm{Can}_0$, $G\mapsto G_{\mathrm{can}}$, $\Phi_0$ on positive definite rational Gram matrices, and a deterministic machine that on a rank-$r$ matrix $G$ of encoding length $\ell$ computes $\mathrm{Can}_0(G)$, $G_{\mathrm{can}}$ and a duplicate-free list $\Phi_0(G)$ within
--
--   $$(r+2)^{C(r+2)}(\ell+1)^K$$
--
--   steps, where $\Phi_0(G)$ is exactly the set of isometries from $G$ to $G_{\mathrm{can}}$. For two matrices, $\mathrm{Can}_0(G_1)=\mathrm{Can}_0(G_2)$ if and only if $\mathrm{Iso}(G_1,G_2)\ne\emptyset$, and in the equal case $G_{\mathrm{can}}$ agrees and
--
--   $$\mathrm{Iso}(G_1,G_2)=\{\phi_2^{-1}\phi_1:\phi_i\in\Phi_0(G_i)\}.$$
--
--   This handles the small residual lattices, and every instance of rank below a constant.
--
--   Differences from the source:
--   - reading: a deterministic algorithm, in an unnamed machine model → one Mathlib TM2 machine, with runs counted per input (Turing.TM2OutputsInTime); reason: the paper names no model; TM2 is the strongest standard reading, and every step of the canonicalizer costs r^{O(r)} times a polynomial, a class closed under the polynomial overhead of simulating it on stacks, so the bound survives
--   - encoding: time r^{O(r)} plus output → (r+2)^{C(r+2)}·(ℓ+1)^K, with the output inside; reason: r^{O(r)} is degenerate at r ≤ 1; (ℓ+1)^K is the factor of Remark 2.2; the output has at most Baut(r) matrices of polynomial bit length
--   - reading: a complete transporter list → a duplicate-free list with exactly that set; reason: the construction removes duplicates by sorting (Lemma B.2, p.56)
--   - encoding: a rank-r rational lattice L → its positive definite rational Gram matrix, with isometries as integer matrices U, G = U⊤G_canU; reason: §2.2, p.10; the canonical representative is (ℤʳ, G), p.56
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 5.12, pp.27–28 and p.56

import Mathlib
import Definitions.Def_LIPAlgorithm_encInst
import Definitions.Def_LIPAlgorithm_RunsWithin

namespace LIPAlgorithm

/-- **Theorem 5.12 (Haviv–Regev-derived lattice canonicalizer).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript
sha256 61ee52aa…), Theorem 5.12, pp.27–28 (PDF pp.30–31), restated pp.56 (PDF p.59).

There are functions `Can₀`, `G ↦ G_can`, `Φ₀` and a deterministic machine that, on a rank-`r` positive definite rational Gram
matrix `G`, outputs `(Can₀(G), G_can, Φ₀(G))` within `(r+2)^{C(r+2)}·(ℓ+1)^K` steps, where `Φ₀(G)` is a duplicate-free list of
exactly the isometries from `G` to `G_can`. Moreover `Can₀(G₁) = Can₀(G₂) ⇔ Iso(G₁, G₂) ≠ ∅`, equal strings have the same `G_can`,
and in that case `Iso(G₁, G₂) = {ϕ₂⁻¹ϕ₁ : ϕᵢ ∈ Φ₀(Gᵢ)}`.

**Formalization Note.** `(r+2)` replaces `r`, since `r^{O(r)}` is degenerate at `r ∈ {0, 1}`, and `(ℓ+1)^K` is the polynomial
factor of Remark 2.2, p.10. "Plus output" is inside the bound: `|Φ₀| ≤ Baut(r)` (Corollary 2.12) and the entries of the transporters
have polynomial bit length, so the output fits. Different ranks have different strings, which is the "⇐" for `Iso = ∅`.
The inverse is the integer matrix inverse, which is the true inverse on `GL_r(Z)`. -/
theorem theorem_5_12 :
    ∃ (can : ∀ r : ℕ, RatGram r → List Bool) (Gcan : ∀ r : ℕ, RatGram r → RatGram r)
      (Φ : ∀ r : ℕ, RatGram r → List (Gram r)) (M : Turing.TM2ComputableAux Bool Bool) (C K : ℕ),
      (∀ (r : ℕ) (G : RatGram r), IsRatGram G →
        RunsWithin M (encRatGram G) (encString (can r G) ++ encRatGram (Gcan r G) ++ encMatList (Φ r G))
          ((r + 2) ^ (C * (r + 2)) * ((encRatGram G).length + 1) ^ K)) ∧
      (∀ (r : ℕ) (G : RatGram r), IsRatGram G →
        IsRatGram (Gcan r G) ∧ (Φ r G).Nodup ∧ ∀ U, U ∈ Φ r G ↔ U ∈ ratIsoSet G (Gcan r G)) ∧
      (∀ (r₁ r₂ : ℕ) (G₁ : RatGram r₁) (G₂ : RatGram r₂), IsRatGram G₁ → IsRatGram G₂ →
        can r₁ G₁ = can r₂ G₂ → r₁ = r₂) ∧
      (∀ (r : ℕ) (G₁ G₂ : RatGram r), IsRatGram G₁ → IsRatGram G₂ →
        (can r G₁ = can r G₂ ↔ (ratIsoSet G₁ G₂).Nonempty)) ∧
      (∀ (r : ℕ) (G₁ G₂ : RatGram r), IsRatGram G₁ → IsRatGram G₂ → can r G₁ = can r G₂ →
        Gcan r G₁ = Gcan r G₂ ∧
          ∀ U, U ∈ ratIsoSet G₁ G₂ ↔ ∃ ϕ₁ ∈ Φ r G₁, ∃ ϕ₂ ∈ Φ r G₂, U = ϕ₂⁻¹ * ϕ₁) := by sorry

end LIPAlgorithm
