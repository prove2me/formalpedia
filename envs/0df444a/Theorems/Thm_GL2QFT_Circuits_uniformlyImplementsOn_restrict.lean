-- Prove2me | Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_restrict
-- name    : GL2QFT.Circuits.uniformlyImplementsOn_restrict
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:43.655484+00:00
-- url     : https://prove2.me/theorems/404292ab-5ab5-4cab-b24a-da1a66ffed3f
-- title:
--   Domain/codomain restriction of `UniformlyImplementsOn` along injective embeddings
-- statement:
--   Suppose a uniform Clifford+$T$ circuit family implements $\Phi(D) : \mathbb{C}^{X(D)} \to \mathbb{C}^{Y(D)}$ on $P(D)$ with codes $c_{\mathrm{in}}, c_{\mathrm{out}}$. Let $\iota_X(D) : X'(D) \hookrightarrow X(D)$ and $\iota_Y(D) : Y'(D) \hookrightarrow Y(D)$ be injective embeddings whenever $P(D)$ holds such that $\Phi(D)$ maps $\operatorname{im}(\iota_X(D))$ into $\operatorname{im}(\iota_Y(D))$, i.e.
--
--   $$\Phi(D)_{y,\,\iota_X(D)(x')} = 0 \quad \forall y \notin \operatorname{im}(\iota_Y(D)).$$
--
--   Then the restricted family $\Phi(D) \circ \iota_X(D)$ restricted to rows $\iota_Y(D)$ is uniformly implemented on $P$ with codes $c_{\mathrm{in}} \circ \iota_X$ and $c_{\mathrm{out}} \circ \iota_Y$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.1–6.4.2 (pp. 41–44), restriction of partial isometries and subspace codes

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem uniformlyImplementsOn_restrict {P : FieldData → Prop} {X Y X' Y' : FieldData → Type} [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] [∀ D, Fintype (X' D)] [∀ D, Fintype (Y' D)] {inW outW : FieldData → ℕ} {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)} {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (ιX : ∀ D, X' D → X D) (ιY : ∀ D, Y' D → Y D) (h : UniformlyImplementsOn P cin cout Φ) (hιX : ∀ D, P D → Function.Injective (ιX D)) (hιY : ∀ D, P D → Function.Injective (ιY D)) (hinv : ∀ D, P D → ∀ x' y, (∀ y', ιY D y' ≠ y) → Φ D y (ιX D x') = 0) : UniformlyImplementsOn P (fun D x' => cin D (ιX D x')) (fun D y' => cout D (ιY D y')) (fun D => (Φ D).submatrix (ιY D) (ιX D)) := by sorry

end Circuits
end GL2QFT
