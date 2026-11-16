-- Prove2me | Theorems.Thm_MatrixQuantumSampler595_Correspondence_Supplement_multilinear_weak_design
-- name    : MatrixQuantumSampler595.Correspondence.Supplement.multilinear_weak_design
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:59:35.333499+00:00
-- url     : https://prove2.me/theorems/eaf71871-f208-4f73-844b-27056abdaad0
-- title:
--   Theorem 4.4 — multilinear weak-design extraction
-- statement:
--   Let $n,\lambda,\ell,M,m_0\ge1$ be integers with $n\le\lambda2^\ell$ and $m_0\le\lambda$. Let $S_1,\ldots,S_M\subseteq[v]$ be an $(\ell,\varrho)$ weak design, and let real $0\le k\le n$ and $\eta>0$ satisfy
--
--   $$\frac M2\sqrt{2^{m_0}\left(2^{\lambda\varrho M-k}+\ell2^{-\lambda}\right)}\le\eta.$$
--
--   There exists a strong conditional-min-entropy quantum-proof $(k,\eta)$ extractor
--
--   $$\mathrm{Ext}:\{0,1\}^n\times\{0,1\}^{\lambda(v+1)}\longrightarrow\{0,1\}^{Mm_0}.$$
--
--   This companion preserves the exact seed/output lengths and the complete error expression for every supplied weak design. The error is not restricted to at most one half. There is no additional polynomial-time assertion in this theorem.
--
--   Differences from the source:
--   - encoding: binary source, seed and output strings with one-based sample/coordinate labels → Fin-indexed Boolean strings and a uniform Fin(2^d) seed alphabet with zero-based labels; reason: finite relabelling preserves all states, probabilities and maps
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), Theorem 4.4, printed/PDF p.18; pp.18–20

import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_ConditionalExtractor
import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_UniformConstruction
import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_WeakDesign

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- Theorem 4.4, p.18. Exact lengths and full hybrid error bound (4.3). -/
theorem multilinear_weak_design
    (n lam ell M m0 v : ℕ) (hn : 1 ≤ n) (hlam : 1 ≤ lam) (hell : 1 ≤ ell)
    (hM : 1 ≤ M) (hm0 : 1 ≤ m0) (hsize : n ≤ lam * 2 ^ ell) (hproj : m0 ≤ lam)
    (rho : ℝ) (S : Fin M → Finset (Fin v)) (hdesign : IsWeakDesign S ell rho)
    (k eta : ℝ) (hk : 0 ≤ k) (hkn : k ≤ n) (heta : 0 < eta)
    (herror : (M : ℝ) / 2 * Real.sqrt ((2 : ℝ) ^ m0 *
      ((2 : ℝ) ^ ((lam : ℝ) * rho * M - k) + (ell : ℝ) * (2 : ℝ) ^ (-(lam : ℝ)))) ≤ eta) :
    ∃ F : BitString n → Fin (2 ^ (lam * (v + 1))) → BitString (M * m0),
      IsStrongConditionalExtractor F k eta := by sorry

end MatrixQuantumSampler595.Correspondence.Supplement
