-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_A_2
-- name    : IntuitiveDPI.Smooth.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:31.53112+00:00
-- url     : https://prove2.me/theorems/eb1524c4-77eb-4b9f-8507-02f12bfd377c
-- title:
--   Lemma A.2, p. 9 — P(ρ, σ) ≥ P(ρ, σ̃), σ̃ the eigenvalues of σ on the eigenbasis of ρ, both sorted
-- statement:
--   Let $\rho,\sigma$ be density matrices on $\mathbb C^d$ with eigen-decompositions $\rho=\sum_i r_i|i\rangle\langle i|$ and $\sigma=\sum_i s_i|v_i\rangle\langle v_i|$, the eigenvalues listed in non-increasing order ($r_{i+1}\le r_i$, $s_{i+1}\le s_i$). Define $\tilde\sigma=\sum_i s_i|i\rangle\langle i|$, the eigenvalues of $\sigma$ placed on the eigenvectors of $\rho$ in matching order. Then
--   $$P(\rho,\sigma)\ge P(\rho,\tilde\sigma).$$
--
--   Equivalently the fidelity increases when $\sigma$ is rotated to commute with $\rho$ with eigenvalues aligned; the paper uses this to reduce the almost-i.i.d. limit (Lemma B.1) to classical distributions.
--
--   **Formalization Note** The eigen-decompositions are given as data: unitaries $U,V$ (columns the eigenvectors) and antitone eigenvalue lists $r,s:\{0,\dots,d-1\}\to\mathbb R$ with $\rho=U\operatorname{diag}(r)U^\dagger$, $\sigma=V\operatorname{diag}(s)V^\dagger$; then $\tilde\sigma=U\operatorname{diag}(s)U^\dagger$. The page writes "where $|i\rangle$ are the eigenvalues of $\rho$", a slip for eigenvectors.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 9, Lemma A.2, (A.3)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma A.2, (A.3), p. 9: let `ρ = U diag(r) U†` and `σ = V diag(s) V†` be density
matrices with eigenvalues `r, s` in non-increasing order, and `σ̃ = U diag(s) U†` (the eigenvalues
of `σ` placed on the eigenvectors of `ρ`). Then `P(ρ, σ) ≥ P(ρ, σ̃)`. -/
theorem lemma_A_2 {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r s : Fin d → ℝ) (hr : Antitone r) (hs : Antitone s)
    (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (hρU : ρ = U * Matrix.diagonal (fun i => (r i : ℂ)) * Uᴴ)
    (hσV : σ = V * Matrix.diagonal (fun i => (s i : ℂ)) * Vᴴ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    purifiedDistance ρ (U * Matrix.diagonal (fun i => (s i : ℂ)) * Uᴴ) ≤
      purifiedDistance ρ σ := by sorry

end IntuitiveDPI.Smooth
